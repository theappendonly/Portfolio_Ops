-- Gini / AUC test for Postgres: one file, no extensions needed.
-- Run the whole file once. It creates four functions in public:
--   ln_gamma, chi_square_sf, chi_square_critical  (helpers for the p-value and confidence interval)
--   gini_auc_test(group_a numeric[], group_b numeric[], alpha numeric default 0.05)
-- group_a = the "bad" outcome (e.g. denied), group_b = the "good" outcome (e.g. approved).
-- AUC > 0.5 means group_a tends to have the higher values. Gini = 2 * AUC - 1.
--
-- Example:
--   select * from public.gini_auc_test(
--       (select array_agg(dti) from applications where not approved),
--       (select array_agg(dti) from applications where approved));

CREATE OR REPLACE FUNCTION public.ln_gamma(x double precision)
 RETURNS double precision
 LANGUAGE plpgsql
 IMMUTABLE STRICT
AS $function$
declare
    c double precision[] := array[0.99999999999980993, 676.5203681218851, -1259.1392167224028,
        771.32342877765313, -176.61502916214059, 12.507343278686905, -0.13857109526572012,
        9.9843695780195716e-6, 1.5056327351493116e-7];
    a double precision; t double precision; y double precision := x - 1;
begin
    a := c[1];
    for i in 1..8 loop a := a + c[i+1] / (y + i); end loop;
    t := y + 7.5;
    return 0.5 * ln(2 * pi()) + (y + 0.5) * ln(t) - t + ln(a);
end $function$

;

CREATE OR REPLACE FUNCTION public.chi_square_sf(x double precision, df integer)
 RETURNS double precision
 LANGUAGE plpgsql
 IMMUTABLE STRICT
AS $function$
declare
    a double precision := df / 2.0; z double precision := x / 2.0;
    gln double precision; lead double precision;
    ap double precision; s double precision; del double precision;
    b double precision; c double precision; d double precision; h double precision; an double precision;
    eps constant double precision := 1e-15; fpmin constant double precision := 1e-300;
begin
    if x <= 0 then return 1.0; end if;
    gln := public.ln_gamma(a);
    lead := -z + a * ln(z) - gln;
    if lead < -700 then return 0.0; end if;               -- below double precision range
    if z < a + 1 then                                      -- series for P, return 1 - P
        ap := a; s := 1.0 / a; del := s;
        for i in 1..10000 loop
            ap := ap + 1; del := del * z / ap; s := s + del;
            exit when abs(del) < abs(s) * eps;
        end loop;
        return greatest(0.0, 1.0 - s * exp(lead));
    else                                                   -- Lentz continued fraction for Q
        b := z + 1 - a; c := 1.0 / fpmin; d := 1.0 / b; h := d;
        for i in 1..10000 loop
            an := -i * (i - a); b := b + 2;
            d := an * d + b; if abs(d) < fpmin then d := fpmin; end if;
            c := b + an / c; if abs(c) < fpmin then c := fpmin; end if;
            d := 1.0 / d; del := d * c; h := h * del;
            exit when abs(del - 1.0) < eps;
        end loop;
        return least(1.0, exp(lead) * h);
    end if;
end $function$
;

CREATE OR REPLACE FUNCTION public.chi_square_critical(alpha double precision, df integer)
 RETURNS double precision
 LANGUAGE plpgsql
 IMMUTABLE STRICT
AS $function$
declare lo double precision := 0; hi double precision := df + 10 * sqrt(2.0 * df) + 50; mid double precision;
begin
    while public.chi_square_sf(hi, df) > alpha loop hi := hi * 2; end loop;
    for i in 1..200 loop
        mid := (lo + hi) / 2;
        if public.chi_square_sf(mid, df) > alpha then lo := mid; else hi := mid; end if;
        exit when hi - lo < 1e-10;
    end loop;
    return (lo + hi) / 2;
end $function$

;

CREATE OR REPLACE FUNCTION public.gini_auc_test(group_a numeric[], group_b numeric[], alpha numeric DEFAULT 0.05)
 RETURNS TABLE(n_a integer, n_b integer, auc numeric, gini numeric, auc_se numeric, auc_ci_lower numeric, auc_ci_upper numeric, gini_ci_lower numeric, gini_ci_upper numeric, z_statistic numeric, p_value double precision, significant boolean, conclusion text)
 LANGUAGE plpgsql
 STABLE
AS $function$
declare
    na integer; nb integer; u double precision; var_a double precision; var_b double precision;
    tie_term double precision; big_n double precision; a_auc double precision; se double precision;
    sigma double precision; z double precision; p double precision; z_crit double precision;
    lo double precision; hi double precision;
begin
    with pooled as (
        select v, 'a' g from unnest(group_a) v where v is not null
        union all
        select v, 'b' g from unnest(group_b) v where v is not null
    ), ranked as (
        select g, v,
               rank() over (order by v) + (count(*) over (partition by v) - 1) / 2.0 r_all,
               rank() over (partition by g order by v) + (count(*) over (partition by g, v) - 1) / 2.0 r_own
        from pooled
    ), sizes as (
        select count(*) filter (where g = 'a') na, count(*) filter (where g = 'b') nb from pooled
    ), ties as (
        select sum(t ^ 3 - t) tie_term from (select count(*)::double precision t from pooled group by v) x
    ), placed as (
        -- DeLong placement: share of the other group this value beats, ties counting half
        select g, sum(r_all) sum_rank,
               var_samp(((r_all - r_own) / case when g = 'a' then s.nb else s.na end)::double precision) var_p
        from ranked cross join sizes s group by g, s.na, s.nb
    )
    select s.na, s.nb,
           (select sum_rank from placed where g = 'a') - s.na * (s.na + 1) / 2.0,
           (select var_p from placed where g = 'a'),
           (select var_p from placed where g = 'b'),
           t.tie_term
      into na, nb, u, var_a, var_b, tie_term
      from sizes s cross join ties t;

    if na < 2 or nb < 2 then
        raise exception 'Need at least 2 non-null values in each group, got % and %', na, nb;
    end if;

    big_n := na + nb;
    a_auc := u / (na::double precision * nb);
    se := sqrt(var_a / na + var_b / nb);

    -- Null-hypothesis test of AUC = 0.5: Mann-Whitney normal approximation with
    -- tie correction, no continuity correction. A squared z is chi-square with 1 df.
    sigma := sqrt(na::double precision * nb / 12.0 * ((big_n + 1) - tie_term / (big_n * (big_n - 1))));
    if sigma > 0 then
        z := (u - na::double precision * nb / 2.0) / sigma;
        p := public.chi_square_sf(z * z, 1);
    else
        z := 0; p := 1;   -- every value tied, no ordering to test
    end if;

    z_crit := sqrt(public.chi_square_critical(alpha::double precision, 1));
    lo := greatest(0.0, a_auc - z_crit * se);
    hi := least(1.0, a_auc + z_crit * se);

    if least(na, nb) < 20 then
        raise notice 'Smallest group has only % values; treat the p-value and interval as indicative.', least(na, nb);
    end if;
    if se = 0 and sigma > 0 then
        raise notice 'The groups are perfectly separated, so the standard error is 0 and the interval has no width. That is not certainty.';
    end if;

    return query select na, nb, round(a_auc::numeric, 6), round((2 * a_auc - 1)::numeric, 6),
        round(se::numeric, 6), round(lo::numeric, 6), round(hi::numeric, 6),
        round((2 * lo - 1)::numeric, 6), round((2 * hi - 1)::numeric, 6),
        round(z::numeric, 4), p, p < alpha,
        case when p >= alpha then 'Fail to reject the null hypothesis: the score does not significantly separate the two groups.'
             when a_auc > 0.5 then 'Reject the null hypothesis: group_a tends to score higher than group_b.'
             else 'Reject the null hypothesis: group_a tends to score lower than group_b.' end;
end
$function$

;
