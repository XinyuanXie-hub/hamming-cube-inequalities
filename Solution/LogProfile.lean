import Mathlib
namespace HammingCubeLog
noncomputable def L (t : ℝ) : ℝ := t * Real.sqrt (Real.logb 2 (1 / t))
lemma L_zero : L 0 = 0 := by simp [L]
lemma L_one : L 1 = 0 := by simp [L]
lemma L_half : L (1 / 2) = 1 / 2 := by norm_num [L, Real.logb_self_eq_one]
lemma L_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ L t := mul_nonneg ht (Real.sqrt_nonneg _)
lemma L_sqrt_form {t : ℝ} (ht : 0 ≤ t) :
    L t = Real.sqrt (-t * (t * Real.log t) / Real.log 2) := by
  rw [L, Real.logb, one_div, Real.log_inv]
  conv_lhs => lhs; rw [← Real.sqrt_sq ht]
  rw [← Real.sqrt_mul (sq_nonneg t)]
  congr 1
  ring
lemma L_continuousOn : ContinuousOn L (Set.Ici 0) := by
  have h : Continuous (fun t : ℝ => Real.sqrt (-t * (t * Real.log t) / Real.log 2)) :=
    Real.continuous_sqrt.comp ((continuous_id.neg.mul Real.continuous_mul_log).div_const _)
  exact h.continuousOn.congr (fun t ht => L_sqrt_form ht)
lemma L_hasDerivAt {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    HasDerivAt L
      (Real.sqrt (Real.logb 2 (1 / t)) -
        1 / (2 * Real.log 2 * Real.sqrt (Real.logb 2 (1 / t)))) t := by
  have hn : t ≠ 0 := ne_of_gt ht
  have hl : 0 < Real.logb 2 (1 / t) := by
    apply Real.logb_pos (by norm_num)
    exact (one_lt_div ht).mpr ht1
  have hd : HasDerivAt (fun x : ℝ => Real.logb 2 (1 / x))
      (-(1 / t) / Real.log 2) t := by
    simp only [Real.logb, one_div, Real.log_inv]
    exact ((Real.hasDerivAt_log hn).neg).div_const _
  have hh := (hasDerivAt_id t).mul ((Real.hasDerivAt_sqrt (ne_of_gt hl)).comp t hd)
  convert hh using 1
  · rfl
  · dsimp
    field_simp
    ring
lemma L_concaveOn : ConcaveOn ℝ (Set.Icc 0 1) L := by
  apply AntitoneOn.concaveOn_of_deriv (convex_Icc 0 1)
      (L_continuousOn.mono (fun _ h => h.1))
  · intro x hx
    rw [interior_Icc] at hx
    exact (L_hasDerivAt hx.1 hx.2).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro x hx y hy hxy
    rw [(L_hasDerivAt hx.1 hx.2).deriv, (L_hasDerivAt hy.1 hy.2).deriv]
    have hs : Real.sqrt (Real.logb 2 (1 / y)) ≤ Real.sqrt (Real.logb 2 (1 / x)) := by
      apply Real.sqrt_le_sqrt
      apply Real.logb_le_logb_of_le (by norm_num) (one_div_pos.mpr hy.1)
      exact one_div_le_one_div_of_le hx.1 hxy
    have hp : 0 < Real.logb 2 (1 / y) :=
      Real.logb_pos (by norm_num) ((one_lt_div hy.1).mpr hy.2)
    have hc : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hi : 1 / (2 * Real.log 2 * Real.sqrt (Real.logb 2 (1 / x))) ≤
        1 / (2 * Real.log 2 * Real.sqrt (Real.logb 2 (1 / y))) := by
      apply one_div_le_one_div_of_le
      · positivity
      · exact mul_le_mul_of_nonneg_left hs (by positivity)
    linarith
lemma L_two_point_zero {y : ℝ} (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    Real.sqrt (y ^ 2 + L y ^ 2) + L 0 = 2 * L (y / 2) := by
  rcases eq_or_lt_of_le hy with he | hp
  · subst y; simp [L_zero]
  have hn : y ≠ 0 := ne_of_gt hp
  have hl : 0 ≤ Real.logb 2 (1 / y) := by
    apply Real.logb_nonneg (by norm_num)
    exact (one_le_div hp).mpr hy1
  have hd : Real.logb 2 (1 / (y / 2)) = 1 + Real.logb 2 (1 / y) := by
    have hr : 1 / (y / 2) = 2 * (1 / y) := by ring
    rw [hr, Real.logb_mul (by norm_num) (one_div_ne_zero hn)]
    norm_num [Real.logb_self_eq_one]
  rw [L_zero, add_zero]
  unfold L
  rw [mul_pow, Real.sq_sqrt hl, hd]
  have hr : y ^ 2 + y ^ 2 * Real.logb 2 (1 / y) =
      y ^ 2 * (1 + Real.logb 2 (1 / y)) := by ring
  rw [hr, Real.sqrt_mul (sq_nonneg y), Real.sqrt_sq hy]
  ring
lemma neg_log_one_sub_lower {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) :
    s + s ^ 2 / 2 ≤ -Real.log (1 - s) := by
  let g : ℝ → ℝ := fun t => -Real.log (1-t) - t - t^2/2
  have hd (t : ℝ) (ht : t < 1) :
      HasDerivAt g (1 / (1-t) - 1 - t) t := by
    have hlog := (Real.hasDerivAt_log (by linarith : 1-t ≠ 0)).comp t
      ((hasDerivAt_const t 1).sub (hasDerivAt_id t))
    have hh := (hlog.neg.sub (hasDerivAt_id t)).sub
      (((hasDerivAt_id t).pow 2).div_const 2)
    convert hh using 1
    · ext x; simp [g, Function.comp_def]
    · dsimp; ring
  have hm : MonotoneOn g (Set.Icc 0 s) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 s)
    · intro t ht
      exact (hd t (lt_of_le_of_lt ht.2 hs1)).continuousAt.continuousWithinAt
    · intro t ht
      have ht' : t ∈ Set.Icc 0 s := interior_subset ht
      exact (hd t (lt_of_le_of_lt ht'.2 hs1)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : t ∈ Set.Icc 0 s := interior_subset ht
      rw [(hd t (lt_of_le_of_lt ht'.2 hs1)).deriv]
      have hp : 0 < 1-t := by linarith [ht'.2]
      have he : 1 / (1-t) - 1 - t = t^2/(1-t) := by field_simp; ring
      rw [he]
      positivity
  have h := hm (show (0:ℝ) ∈ Set.Icc 0 s from ⟨le_rfl,hs⟩)
    (show s ∈ Set.Icc 0 s from ⟨hs,le_rfl⟩) hs
  dsimp [g] at h
  norm_num at h
  linarith
lemma sqrt_product_shift {A B d : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hd : 0 ≤ d) :
    Real.sqrt A * Real.sqrt B + d ≤ Real.sqrt (A+d) * Real.sqrt (B+d) := by
  have hsa := Real.sq_sqrt hA
  have hsb := Real.sq_sqrt hB
  have hsc := Real.sq_sqrt (add_nonneg hA hd)
  have hse := Real.sq_sqrt (add_nonneg hB hd)
  have ham : 2 * Real.sqrt A * Real.sqrt B ≤ A+B := by
    nlinarith [sq_nonneg (Real.sqrt A - Real.sqrt B)]
  have hmul := mul_nonneg hd (sub_nonneg.mpr ham)
  have hp : (Real.sqrt A * Real.sqrt B)^2 = A*B := by rw [mul_pow,hsa,hsb]
  have hq : (Real.sqrt (A+d) * Real.sqrt (B+d))^2 = (A+d)*(B+d) := by
    rw [mul_pow,hsc,hse]
  have hpos : 0 ≤ Real.sqrt (A+d) * Real.sqrt (B+d) := by positivity
  nlinarith [sq_nonneg (Real.sqrt A * Real.sqrt B + d - Real.sqrt (A+d) * Real.sqrt (B+d))]

lemma sqrt_weighted_shift {u v t a : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (ht : 0 ≤ t) (ha : 1 ≤ a) :
    (Real.sqrt (1+u) + t * Real.sqrt (1+v))^2 - (1+t)^2 ≤
    (Real.sqrt (a+u) + t * Real.sqrt (a+v))^2 - (1+t)^2*a := by
  have h := sqrt_product_shift (show 0 ≤ 1+u by linarith)
    (show 0 ≤ 1+v by linarith) (show 0 ≤ a-1 by linarith)
  have he (z : ℝ) : 1+z+(a-1) = a+z := by ring
  rw [he, he] at h
  have hm := mul_nonneg ht (sub_nonneg.mpr h)
  have h1 := Real.sq_sqrt (show 0 ≤ 1+u by linarith)
  have h2 := Real.sq_sqrt (show 0 ≤ 1+v by linarith)
  have h3 := Real.sq_sqrt (show 0 ≤ a+u by linarith)
  have h4 := Real.sq_sqrt (show 0 ≤ a+v by linarith)
  nlinarith [congrArg (fun z : ℝ => t^2*z) h2, congrArg (fun z : ℝ => t^2*z) h4]
lemma sqrt_weighted_lift {u v w t a : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hw : 0 ≤ w) (ht : 0 ≤ t) (ha : 1 ≤ a)
    (hbase : (1+t)*Real.sqrt (1+w) ≤ Real.sqrt (1+u)+t*Real.sqrt (1+v)) :
    (1+t)*Real.sqrt (a+w) ≤ Real.sqrt (a+u)+t*Real.sqrt (a+v) := by
  have hshift := sqrt_weighted_shift hu hv ht ha
  have hsq := sq_le_sq₀ (show 0 ≤ (1+t)*Real.sqrt (1+w) by positivity)
    (show 0 ≤ Real.sqrt (1+u)+t*Real.sqrt (1+v) by positivity)
  have hb := hsq.mpr hbase
  rw [mul_pow, Real.sq_sqrt (show 0 ≤ 1+w by linarith)] at hb
  apply (sq_le_sq₀ (show 0 ≤ (1+t)*Real.sqrt (a+w) by positivity)
    (show 0 ≤ Real.sqrt (a+u)+t*Real.sqrt (a+v) by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (show 0 ≤ a+w by linarith)]
  nlinarith
lemma log_quartic_nonpos (c s : ℝ) (hc0 : 69 / 100 ≤ c) (hc1 : c ≤ 7 / 10)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    4*(c-1)^2*s^4 + 12*(1-c)*(2*c-1)*s^3 - (17-18*c)*(2*c-1)*s^2 -
      (12-24*c+16*c^2)*s + 32*c^2-32*c+4 ≤ 0 := by
  have hc2 : c^2 ≤ 49/100 := by nlinarith
  have b0 : 32*c^2-32*c+4 ≤ 0 := by nlinarith
  have b1 : 28*c^2-26*c+1 ≤ 0 := by nlinarith
  have b2 : 30*c^2-86*c/3+5/6 ≤ 0 := by nlinarith
  have b3 : 32*c^2-31*c+1/2 ≤ 0 := by nlinarith
  have b4 : 32*c^2-32*c+1 ≤ 0 := by nlinarith
  have h0 := mul_nonpos_of_nonpos_of_nonneg b0 (sq_nonneg ((1-s)^2))
  have h1 := mul_nonpos_of_nonpos_of_nonneg b1 (show 0 ≤ 4*s*(1-s)^3 by positivity)
  have h2 := mul_nonpos_of_nonpos_of_nonneg b2 (show 0 ≤ 6*s^2*(1-s)^2 by positivity)
  have h3 := mul_nonpos_of_nonpos_of_nonneg b3 (show 0 ≤ 4*s^3*(1-s) by positivity)
  have h4 := mul_nonpos_of_nonpos_of_nonneg b4 (show 0 ≤ s^4 by positivity)
  nlinarith only [h0,h1,h2,h3,h4]

lemma log_sqrt_polynomial (c s : ℝ) (hc0 : 69 / 100 ≤ c) (hc1 : c ≤ 7 / 10)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (2-s)*Real.sqrt (1+s/(2*c)+(1-1/(2*c))*s^2) ≤
      Real.sqrt (1+s^2)+(1-s)*Real.sqrt (1+s/c+s^2/(2*c)) := by
  have hc : 0 < c := by linarith
  let A := 1+s^2
  let B := 1+s/c+s^2/(2*c)
  let C := 1+s/(2*c)+(1-1/(2*c))*s^2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hcc : 0 ≤ 1-1/(2*c) := by
    rw [sub_nonneg, div_le_one (by positivity)]; linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have ha := Real.sq_sqrt hA
  have hb := Real.sq_sqrt hB
  have hcc' := Real.sq_sqrt hC
  have hav := Real.sqrt_nonneg A
  have hbv := Real.sqrt_nonneg B
  have hcv := Real.sqrt_nonneg C
  have hp := log_quartic_nonpos c s hc0 hc1 hs0 hs1
  have factor : 4*(1-s)^2*A*B - ((2-s)^2*C-A-(1-s)^2*B)^2 =
      -(s^2*(1-s)^2/(4*c^2)) *
        (4*(c-1)^2*s^4 + 12*(1-c)*(2*c-1)*s^3 - (17-18*c)*(2*c-1)*s^2 -
         (12-24*c+16*c^2)*s + 32*c^2-32*c+4) := by
    dsimp [A,B,C]
    field_simp
    ring
  have hf : 0 ≤ 4*(1-s)^2*A*B - ((2-s)^2*C-A-(1-s)^2*B)^2 := by
    rw [factor]
    exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (by positivity)) hp
  have hab : 0 ≤ (1-s)*Real.sqrt A*Real.sqrt B := by positivity
  have he : (Real.sqrt A * Real.sqrt B)^2 = A*B := by rw [mul_pow,ha,hb]
  have hi : (2-s)^2*C-A-(1-s)^2*B ≤ 2*(1-s)*Real.sqrt A*Real.sqrt B := by
    have he2 : (2*(1-s)*Real.sqrt A*Real.sqrt B)^2 = 4*(1-s)^2*A*B := by
      rw [mul_pow, mul_pow, mul_pow, ha, hb]; ring
    have hab2 : 0 ≤ 2*(1-s)*Real.sqrt A*Real.sqrt B := by positivity
    have hsquare : ((2-s)^2*C-A-(1-s)^2*B)^2 ≤ (2*(1-s)*Real.sqrt A*Real.sqrt B)^2 := by
      rw [he2]; linarith only [hf]
    exact (sq_le_sq₀ (by positivity : 0 ≤ |(2-s)^2*C-A-(1-s)^2*B|) hab2).mp
      (by simpa only [sq_abs] using hsquare) |>.trans' (le_abs_self _)
  change (2-s)*Real.sqrt C ≤ Real.sqrt A+(1-s)*Real.sqrt B
  have hleft : 0 ≤ (2-s)*Real.sqrt C := mul_nonneg (by linarith) hcv
  have hright : 0 ≤ Real.sqrt A+(1-s)*Real.sqrt B := by positivity
  apply (sq_le_sq₀ hleft hright).mp
  nlinarith only [hi, ha, hb, hcc']

theorem neg_log_one_sub_half_le (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    -Real.log (1 - s / 2) ≤ s / 2 + (Real.log 2 - 1 / 2) * s ^ 2 := by
  have series (u : ℝ) (hu : |u| < 1) :
      HasSum (fun n : ℕ => u ^ (n + 2) / (n + 2)) (-Real.log (1 - u) - u) := by
    have h := (hasSum_nat_add_iff' 1).mpr (Real.hasSum_pow_div_log_of_abs_lt_one hu)
    simpa only [Finset.sum_range_one, Nat.cast_zero, zero_add, pow_one, div_one,
      Nat.cast_add, Nat.cast_one, Nat.add_assoc, add_assoc, one_add_one_eq_two] using h
  have hu : |s / 2| < 1 := by rw [abs_of_nonneg (by positivity)]; linarith
  have hleft := series (s / 2) hu
  have hright := (series (1 / 2) (by norm_num)).mul_left (s ^ 2)
  have hcomp : -Real.log (1 - s / 2) - s / 2 ≤
      s ^ 2 * (-Real.log (1 - 1 / 2) - 1 / 2) := by
    apply hasSum_le _ hleft hright
    intro n
    have hp : s ^ n ≤ 1 := pow_le_one₀ hs0 hs1
    calc
      (s / 2) ^ (n + 2) / (n + 2) =
          s ^ 2 * s ^ n * ((1 / 2 : ℝ) ^ (n + 2)) / (n + 2) := by
        rw [show s / 2 = s * (1 / 2) by ring, mul_pow, pow_add]
        ring
      _ ≤ s ^ 2 * 1 * ((1 / 2 : ℝ) ^ (n + 2)) / (n + 2) := by
        gcongr
      _ = s ^ 2 * ((1 / 2 : ℝ) ^ (n + 2) / (n + 2)) := by ring
  have hlog : Real.log (1 - (1 : ℝ) / 2) = -Real.log 2 := by
    rw [show 1 - (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [hlog] at hcomp
  linarith


lemma log_normalized_two_point (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1+t)*Real.sqrt (1+Real.logb 2 (2/(1+t))) ≤
      Real.sqrt (1+(1-t)^2)+t*Real.sqrt (1+Real.logb 2 (1/t)) := by
  rcases eq_or_lt_of_le ht0 with he | ht
  · subst t; norm_num [Real.logb_self_eq_one]
  have hc : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc0 : (69/100 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hc1 : Real.log 2 ≤ (7/10 : ℝ) := by linarith [Real.log_two_lt_d9]
  have hpoly := log_sqrt_polynomial (Real.log 2) (1-t) hc0 hc1
    (by linarith) (by linarith)
  have hlo := neg_log_one_sub_lower (show 0 ≤ 1-t by linarith) (show 1-t < 1 by linarith)
  have hup := neg_log_one_sub_half_le (1-t) (by linarith) (by linarith)
  have hlog1 : Real.logb 2 (1/t) = -Real.log t / Real.log 2 := by
    rw [Real.logb,one_div,Real.log_inv]
  have hlog2 : Real.logb 2 (2/(1+t)) = -Real.log (1-(1-t)/2) / Real.log 2 := by
    have he : 2/(1+t) = (1-(1-t)/2)⁻¹ := by
      rw [show 1-(1-t)/2=(1+t)/2 by ring, inv_div]
    rw [Real.logb,he,Real.log_inv]
  have hlow : 1+(1-t)/Real.log 2+(1-t)^2/(2*Real.log 2) ≤
      1+Real.logb 2 (1/t) := by
    rw [hlog1]
    have he : 1-(1-t)=t := by ring
    rw [he] at hlo
    apply (le_of_sub_nonneg ?_)
    field_simp
    nlinarith
  have hupp : 1+Real.logb 2 (2/(1+t)) ≤
      1+(1-t)/(2*Real.log 2)+(1-1/(2*Real.log 2))*(1-t)^2 := by
    rw [hlog2]
    have hh := div_le_div_of_nonneg_right hup (le_of_lt hc)
    calc
      _ ≤ 1 + ((1-t)/2+(Real.log 2-1/2)*(1-t)^2)/Real.log 2 := by linarith
      _ = _ := by field_simp; ring
  have hp1 := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hupp) (show 0 ≤ 1+t by linarith)
  have hp2 := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hlow) ht0
  have he : 2-(1-t)=1+t := by ring
  have he' : 1-(1-t)=t := by ring
  rw [he,he'] at hpoly
  linarith
lemma L_two_point_scaled {y t : ℝ} (hy : 0 < y) (hy1 : y ≤ 1/2)
    (ht : 0 < t) (ht1 : t ≤ 1) :
    2*L ((y*t+y)/2) ≤ Real.sqrt ((y-y*t)^2+L y^2)+L (y*t) := by
  let a := Real.logb 2 (1/y)
  have ha : 1 ≤ a := by
    have hh : (2 : ℝ) ≤ 1/y := (le_div_iff₀ hy).mpr (by linarith)
    simpa [a, Real.logb_self_eq_one] using
      Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) (by norm_num : (0:ℝ)<2) hh
  have hv : 0 ≤ Real.logb 2 (1/t) := Real.logb_nonneg (by norm_num)
    ((one_le_div ht).mpr ht1)
  have hw : 0 ≤ Real.logb 2 (2/(1+t)) := Real.logb_nonneg (by norm_num)
    ((one_le_div (by linarith : 0 < 1+t)).mpr (by linarith))
  have hh := sqrt_weighted_lift (sq_nonneg (1-t)) hv hw (le_of_lt ht) ha
    (log_normalized_two_point t (le_of_lt ht) ht1)
  have hmul := mul_le_mul_of_nonneg_left hh (le_of_lt hy)
  have hlogt : Real.logb 2 (1/(y*t)) = a+Real.logb 2 (1/t) := by
    rw [show 1/(y*t)= (1/y)*(1/t) by ring,
      Real.logb_mul (by positivity) (by positivity)]
  have hlogm : Real.logb 2 (1/((y*t+y)/2)) = a+Real.logb 2 (2/(1+t)) := by
    have he : 1/((y*t+y)/2)=(1/y)*(2/(1+t)) := by field_simp; ring
    rw [he, Real.logb_mul (by positivity) (by positivity)]
  have hroot : Real.sqrt ((y-y*t)^2+L y^2) = y*Real.sqrt (a+(1-t)^2) := by
    unfold L
    rw [mul_pow, Real.sq_sqrt (show 0 ≤ Real.logb 2 (1/y) by change 0 ≤ a; linarith)]
    have he : (y-y*t)^2+y^2*Real.logb 2 (1/y)=y^2*(a+(1-t)^2) := by dsimp [a]; ring
    rw [he, Real.sqrt_mul (sq_nonneg y), Real.sqrt_sq (le_of_lt hy)]
  rw [hroot]
  unfold L
  rw [hlogt,hlogm]
  nlinarith only [hmul]

lemma L_two_point {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1/2) :
    2*L ((x+y)/2) ≤ Real.sqrt ((y-x)^2+L y^2)+L x := by
  rcases eq_or_lt_of_le hx with he | hp
  · subst x
    simpa using (L_two_point_zero (le_trans (le_refl 0) hxy) (by linarith : y ≤ 1)).ge
  have hyp : 0 < y := lt_of_lt_of_le hp hxy
  have h := L_two_point_scaled hyp hy (div_pos hp hyp) ((div_le_one hyp).mpr hxy)
  simpa [mul_div_cancel₀ _ (ne_of_gt hyp)] using h
lemma logb_upper_cubic {x : ℝ} (hx : 1/4 ≤ x) (hx1 : x ≤ 1/2) :
    Real.logb 2 (1/x) ≤ 1+(1-2*x)/Real.log 2+(4-2/Real.log 2)*(1-2*x)^2 := by
  have hc : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp : 0 < x := by linarith
  have hu := neg_log_one_sub_half_le (2-4*x) (by linarith) (by linarith)
  rw [show 1-(2-4*x)/2=2*x by ring, Real.log_mul (by norm_num) (ne_of_gt hp)] at hu
  rw [Real.logb,one_div,Real.log_inv]
  have hd := div_le_div_of_nonneg_right hu (le_of_lt hc)
  have he : (-(Real.log 2 + Real.log x)) / Real.log 2 = -1 - Real.log x / Real.log 2 := by
    field_simp; ring
  rw [he] at hd
  have he' : ((2-4*x)/2+(Real.log 2-1/2)*(2-4*x)^2)/Real.log 2 =
      (1-2*x)/Real.log 2+(4-2/Real.log 2)*(1-2*x)^2 := by field_simp; ring
  rw [he'] at hd
  simp only [neg_div] at *
  linarith
lemma L_quarter : L (1/4) = Real.sqrt 2 / 4 := by
  unfold L
  have hlog : Real.logb 2 (4 : ℝ) = 2 := by
    rw [show (4:ℝ)=2^2 by norm_num, Real.logb_pow]
    norm_num [Real.logb_self_eq_one]
  norm_num only [one_div_div, div_one]
  rw [hlog]
  ring
lemma log_cubic_polynomial (x r c : ℝ)
    (hx0 : 1/4 ≤ x) (hx1 : x ≤ 1/2)
    (hr0 : 1414/1000 ≤ r) (hr1 : r ≤ 1415/1000) (hr : r^2 = 2)
    (hc0 : 69/100 ≤ c) (hc1 : c ≤ 7/10) :
    let p := (2/3)*(1-x)*(4*r-3+4*(3-2*r)*x)
    0 ≤ p ∧ 1+(1-2*x)/c+(4-2/c)*(1-2*x)^2 ≤ p^2 := by
  dsimp
  have hc : 0 < c := by linarith
  have hcr : 966/1000 ≤ c*r := by
    have h := mul_le_mul (show (69:ℝ)/100 ≤ c from hc0)
      (show (14:ℝ)/10 ≤ r by linarith) (by norm_num) (by linarith : 0 ≤ c)
    norm_num at h
    linarith
  constructor
  · apply mul_nonneg
    · apply mul_nonneg (by norm_num); linarith
    · have ht : 0 ≤ 4*(3-2*r)*x := by
        apply mul_nonneg (by linarith) (by linarith)
      linarith
  · have b0 : 0 ≤ (18*c*r-20*c-3)/3 := by nlinarith only [hcr,hc1]
    have b1 : 0 ≤ (144*c*r-139*c-36)/36 := by nlinarith only [hcr,hc1]
    have b2 : 0 ≤ (8*c*r-6*c-3)/3 := by nlinarith only [hcr,hc1]
    have h0 := mul_nonneg b0 (sq_nonneg (2-4*x))
    have h1 := mul_nonneg b1 (show 0 ≤ 2*(4*x-1)*(2-4*x) by
      apply mul_nonneg <;> linarith)
    have h2 := mul_nonneg b2 (sq_nonneg (4*x-1))
    have hq : 0 ≤ (96*c*r*x^2-192*c*r*x+96*c*r-136*c*x^2+270*c*x-119*c-9)/9 := by
      nlinarith only [h0,h1,h2]
    have hfac := mul_nonneg (show 0 ≤ (4*x-1)*(1-2*x) by
      apply mul_nonneg <;> linarith) hq
    have he : c*((2/3)*(1-x)*(4*r-3+4*(3-2*r)*x))^2 - c - (1-2*x) - (4*c-2)*(1-2*x)^2 =
        (4*x-1)*(1-2*x)*((96*c*r*x^2-192*c*r*x+96*c*r-136*c*x^2+270*c*x-119*c-9)/9) := by
      ring_nf
      simp only [hr]
      ring
    have hd : c * (((2/3)*(1-x)*(4*r-3+4*(3-2*r)*x))^2 -
        (1+(1-2*x)/c+(4-2/c)*(1-2*x)^2)) =
        c*((2/3)*(1-x)*(4*r-3+4*(3-2*r)*x))^2 - c - (1-2*x) - (4*c-2)*(1-2*x)^2 := by
      field_simp
      ring
    have hh : 0 ≤ c * (((2/3)*(1-x)*(4*r-3+4*(3-2*r)*x))^2 -
        (1+(1-2*x)/c+(4-2/c)*(1-2*x)^2)) := by
      rw [hd,he]; exact hfac
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hc).mp hh)
noncomputable def Q (x : ℝ) : ℝ :=
  (2 / 3 : ℝ) * x * (1 - x) *
    (4 * Real.sqrt 2 - 3 + 4 * (3 - 2 * Real.sqrt 2) * x)

lemma L_le_Q {x : ℝ} (hx : 1/4 ≤ x) (hx1 : x ≤ 1/2) : L x ≤ Q x := by
  have hr0 : (1414/1000 : ℝ) ≤ Real.sqrt 2 := by
    apply (Real.le_sqrt (by norm_num) (by norm_num)).mpr
    norm_num
  have hr1 : Real.sqrt 2 ≤ (1415/1000 : ℝ) := by
    apply (Real.sqrt_le_iff).mpr
    norm_num
  have hr : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hc0 : (69/100 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hc1 : Real.log 2 ≤ (7/10 : ℝ) := by linarith [Real.log_two_lt_d9]
  have hp := log_cubic_polynomial x (Real.sqrt 2) (Real.log 2) hx hx1 hr0 hr1 hr hc0 hc1
  dsimp at hp
  have hh := le_trans (logb_upper_cubic hx hx1) hp.2
  have hs := (Real.sqrt_le_iff).mpr ⟨hp.1, hh⟩
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ x by linarith)
  unfold L Q
  nlinarith only [hm]
end HammingCubeLog
