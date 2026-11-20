-- DROP FUNCTION public.adf_test(_numeric, int4, text, numeric);

CREATE OR REPLACE FUNCTION public.adf_test(y numeric[], lags integer DEFAULT NULL::integer, regression text DEFAULT 'c'::text, alpha numeric DEFAULT 0.05)
 RETURNS TABLE(n_obs integer, lags_used integer, regression_type text, adf_statistic numeric, gamma double precision, p_value double precision, critical_1pct numeric, critical_5pct numeric, critical_10pct numeric, significant boolean, conclusion text)
 LANGUAGE plpgsql
 STABLE
AS $function$
declare
    yf double precision[]; t_len integer := cardinality(y);
    with_trend boolean; ntrend integer; maxlag integer; use_lag integer;
    aic double precision; best_aic double precision;
    r record; tau double precision; p double precision; u double precision;
    star double precision; tmin double precision; tmax double precision;
    z double precision; crit double precision[];
    -- MacKinnon 1994 (p-values) and MacKinnon 2010 (critical values), one integrated series
    small double precision[]; large double precision[]; c1 double precision[]; c5 double precision[]; c10 double precision[];
begin
    if t_len is null or array_position(y, null) is not null then
        raise exception 'Series cannot contain nulls, because a gap breaks the lags. Fill or trim it first.';
    end if;
    if lower(regression) = 'c' then
        with_trend := false; ntrend := 1; star := -1.61; tmin := -18.83; tmax := 2.74;
        small := array[2.1659, 1.4412, 0.038269];
        large := array[1.7339, 0.93202, -0.12745, -0.010368];
        c1 := array[-3.43035, -6.5393, -16.786, -79.433];
        c5 := array[-2.86154, -2.8903, -4.234, -40.04];
        c10 := array[-2.56677, -1.5384, -2.809, 0.0];
    elsif lower(regression) = 'ct' then
        with_trend := true; ntrend := 2; star := -2.89; tmin := -16.18; tmax := 0.7;
        small := array[3.2512, 1.6047, 0.049588];
        large := array[2.5261, 0.61654, -0.37956, -0.060285];
        c1 := array[-3.95877, -9.0531, -28.428, -134.155];
        c5 := array[-3.41049, -4.3904, -9.036, -45.374];
        c10 := array[-3.12705, -2.5856, -3.925, -22.38];
    else
        raise exception 'regression must be c (constant) or ct (constant and trend), got %', regression;
    end if;

    select array_agg(v::double precision order by i) into yf from unnest(y) with ordinality u(v, i);

    if lags is not null then
        if lags < 0 then raise exception 'lags cannot be negative, got %', lags; end if;
        use_lag := lags;
    else
        -- Automatic: try 0 to maxlag on a common sample, keep the lowest AIC.
        maxlag := least(ceil(12.0 * (t_len / 100.0) ^ 0.25)::integer, t_len / 2 - ntrend - 1);
        if maxlag < 0 then raise exception 'Series is too short, got % values', t_len; end if;
        for l in 0..maxlag loop
            select * into r from public.adf_regression(yf, l, maxlag + 2, with_trend);
            if r.rss <= 0 then raise exception 'The regression fits perfectly, so the statistic is undefined'; end if;
            aic := r.n_obs * ln(r.rss / r.n_obs) + 2 * r.n_params;
            if best_aic is null or aic < best_aic then best_aic := aic; use_lag := l; end if;
        end loop;
    end if;

    select * into r from public.adf_regression(yf, use_lag, use_lag + 2, with_trend);
    if r.rss <= 0 or r.coef_se[2] = 0 then
        raise exception 'The regression fits perfectly, so the statistic is undefined';
    end if;
    tau := r.coef[2] / r.coef_se[2];

    if tau > tmax then p := 1.0;
    elsif tau < tmin then p := 0.0;
    else
        if tau <= star then z := small[1] + small[2] * tau + small[3] * tau ^ 2;
        else z := large[1] + large[2] * tau + large[3] * tau ^ 2 + large[4] * tau ^ 3;
        end if;
        p := 0.5 * erfc(-z / sqrt(2.0));
    end if;

    u := 1.0 / r.n_obs;
    crit := array[
        c1[1] + c1[2] * u + c1[3] * u ^ 2 + c1[4] * u ^ 3,
        c5[1] + c5[2] * u + c5[3] * u ^ 2 + c5[4] * u ^ 3,
        c10[1] + c10[2] * u + c10[3] * u ^ 2 + c10[4] * u ^ 3
    ];

    if r.n_obs < 50 then
        raise notice 'Only % observations: ADF has little power here, so failing to reject says little.', r.n_obs;
    end if;

    return query select r.n_obs::integer, use_lag, lower(regression), round(tau::numeric, 4), r.coef[2], p,
        round(crit[1]::numeric, 4), round(crit[2]::numeric, 4), round(crit[3]::numeric, 4), p < alpha,
        case when p < alpha
             then 'Reject the null hypothesis: no unit root, the series looks stationary.'
             else 'Fail to reject the null hypothesis: a unit root cannot be ruled out, so the series may be non-stationary.' end;
end
$function$
;
-- DROP FUNCTION public.adf_regression(_float8, int4, int4, bool);

CREATE OR REPLACE FUNCTION public.adf_regression(y double precision[], lag_count integer, first_t integer, with_trend boolean)
 RETURNS TABLE(n_obs integer, n_params integer, coef double precision[], coef_se double precision[], rss double precision)
 LANGUAGE plpgsql
 IMMUTABLE STRICT
AS $function$
-- Regresses the change in y on the prior level, an optional time trend, and lag_count
-- prior changes, over t = first_t to the end. The prior level is always the first
-- regressor, so its coefficient is coef[2].
declare
    t_max integer := cardinality(y); n integer := t_max - first_t + 1;
    base integer := case when with_trend then 2 else 1 end;
    dep double precision[]; xm double precision[]; row_i integer; t integer;
begin
    if first_t < lag_count + 2 then raise exception 'first_t % is too early for % lags', first_t, lag_count; end if;
    if n < 1 then raise exception 'Series is too short for % lags', lag_count; end if;
    dep := array_fill(0::double precision, array[n]);
    xm := array_fill(0::double precision, array[n, base + lag_count]);
    for row_i in 1..n loop
        t := first_t + row_i - 1;
        dep[row_i] := y[t] - y[t - 1];
        xm[row_i][1] := y[t - 1];
        if with_trend then xm[row_i][2] := row_i; end if;
        for l in 1..lag_count loop
            xm[row_i][base + l] := y[t - l] - y[t - l - 1];
        end loop;
    end loop;
    return query select * from public.ols_fit(dep, xm);
end
$function$
;
