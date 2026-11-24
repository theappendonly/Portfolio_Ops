-- DROP FUNCTION public.granger_test(_numeric, _numeric, int4, numeric);

CREATE OR REPLACE FUNCTION public.granger_test(y numeric[], x numeric[], max_lag integer DEFAULT 4, alpha numeric DEFAULT 0.05)
 RETURNS TABLE(lag_order integer, n_obs integer, rss_restricted double precision, rss_unrestricted double precision, f_statistic numeric, df1 integer, df2 integer, critical_value numeric, p_value double precision, significant boolean, conclusion text)
 LANGUAGE plpgsql
 STABLE
AS $function$
declare
    t_len integer := cardinality(y); yf double precision[]; xf double precision[];
    n integer; d2 integer; dep double precision[]; xm double precision[]; t integer;
    r_r double precision; r_u double precision; f double precision; pv double precision;
    adf_p double precision;
begin
    if t_len is null or cardinality(x) is distinct from t_len then
        raise exception 'y and x must be the same length, got % and %', t_len, cardinality(x);
    end if;
    if array_position(y, null) is not null or array_position(x, null) is not null then
        raise exception 'Series cannot contain nulls, because a gap breaks the lags. Fill or trim them first.';
    end if;
    if max_lag < 1 then raise exception 'max_lag must be at least 1, got %', max_lag; end if;
    if t_len - max_lag - 2 * max_lag - 1 < 1 then
        raise exception 'Series is too short for % lags, got % values', max_lag, t_len;
    end if;

    select array_agg(v::double precision order by i) into yf from unnest(y) with ordinality u(v, i);
    select array_agg(v::double precision order by i) into xf from unnest(x) with ordinality u(v, i);

    -- Granger assumes both series are stationary, so warn when one may not be.
    begin
        select a.p_value into adf_p from public.adf_test(y, max_lag) a;
        if adf_p >= 0.05 then
            raise notice 'y may be non-stationary (ADF p = %). Granger can give false positives; consider differencing.', round(adf_p::numeric, 4);
        end if;
        select a.p_value into adf_p from public.adf_test(x, max_lag) a;
        if adf_p >= 0.05 then
            raise notice 'x may be non-stationary (ADF p = %). Granger can give false positives; consider differencing.', round(adf_p::numeric, 4);
        end if;
    exception when others then
        raise notice 'Stationarity check could not run: %', sqlerrm;
    end;

    for lag_n in 1..max_lag loop
        n := t_len - lag_n;
        d2 := n - 2 * lag_n - 1;
        dep := array_fill(0::double precision, array[n]);
        xm := array_fill(0::double precision, array[n, 2 * lag_n]);
        for i in 1..n loop
            t := lag_n + i;
            dep[i] := yf[t];
            for l in 1..lag_n loop
                xm[i][l] := yf[t - l];
                xm[i][lag_n + l] := xf[t - l];
            end loop;
        end loop;

        select o.rss into r_r from public.ols_fit(dep, xm[1:n][1:lag_n]) o;
        select o.rss into r_u from public.ols_fit(dep, xm) o;
        if r_u <= 0 then raise exception 'The regression fits perfectly at lag %, so the F statistic is undefined', lag_n; end if;

        f := greatest(0.0, ((r_r - r_u) / lag_n) / (r_u / d2));
        pv := public.f_sf(f, lag_n, d2);

        lag_order := lag_n; n_obs := n; rss_restricted := r_r; rss_unrestricted := r_u;
        f_statistic := round(f::numeric, 4); df1 := lag_n; df2 := d2;
        critical_value := round(public.f_critical(alpha::double precision, lag_n, d2)::numeric, 4);
        p_value := pv; significant := pv < alpha;
        conclusion := case when pv < alpha
            then 'Reject the null hypothesis: past x helps predict y beyond y''s own past.'
            else 'Fail to reject the null hypothesis: past x adds no significant predictive power for y.' end;
        return next;
    end loop;
end
$function$
;
