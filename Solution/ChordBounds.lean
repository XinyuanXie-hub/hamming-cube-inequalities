import Solution.LogProfile

namespace HammingCubeLog
namespace ChordBounds
theorem log_two_sixteen_thirds_lower :
    (169 : ℝ) / 70 ≤ Real.logb 2 (16 / 3) := by
  have hp : (2 : ℝ)^169 ≤ ((16 : ℝ)/3)^70 := by norm_num
  have hl := Real.logb_le_logb_of_le (b := (2 : ℝ)) (by norm_num)
    (show (0 : ℝ) < 2^169 by positivity) hp
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at hl
  norm_num at hl
  linarith

theorem logProfile_three_sixteenths :
    (2913 : ℝ)/10000 ≤ (3/16 : ℝ) * Real.sqrt (Real.logb 2 (1/(3/16))) := by
  have hl := log_two_sixteen_thirds_lower
  have hs : (1942 : ℝ)/1250 ≤ Real.sqrt (Real.logb 2 (16/3)) := by
    apply (Real.le_sqrt (by norm_num) (by linarith)).mpr
    linarith
  norm_num only [one_div_div] at *
  convert (mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 3/16)) using 1
  norm_num

theorem logProfile_eighth :
    (433 : ℝ)/2000 ≤ (1/8 : ℝ) * Real.sqrt (Real.logb 2 (1/(1/8))) := by
  have hl : Real.logb 2 (1/((1 : ℝ)/8)) = 3 := by
    rw [show 1/((1 : ℝ)/8) = (2 : ℝ)^3 by norm_num, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num)]
    norm_num
  rw [hl]
  have hs : (433 : ℝ)/250 ≤ Real.sqrt 3 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  linarith

theorem logProfile_quarter :
    (7071 : ℝ)/20000 ≤ (1/4 : ℝ) * Real.sqrt (Real.logb 2 (1/(1/4))) := by
  have hl : Real.logb 2 (1/((1 : ℝ)/4)) = 2 := by
    rw [show 1/((1 : ℝ)/4) = (2 : ℝ)^2 by norm_num, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num)]
    norm_num
  rw [hl]
  have hs : (7071 : ℝ)/5000 ≤ Real.sqrt 2 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  linarith

/-- A certificate interface for arbitrary rational logarithmic lower bounds.
The only nontrivial input is an exact integer/rational power comparison. -/
theorem logb_lower_of_power {b x : ℝ} (hb : 1 < b) (_hx : 0 < x)
    (m n : ℕ) (hn : 0 < n) (hp : b^m ≤ x^n) :
    (m : ℝ) / n ≤ Real.logb b x := by
  have hl := Real.logb_le_logb_of_le hb (pow_pos (by linarith : 0 < b) m) hp
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one hb] at hl
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  apply (div_le_iff₀ hn').mpr
  nlinarith

/-- Rational chord-height checker for L(t)=t sqrt(log₂(1/t)). -/
theorem logProfile_lower_of_power {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r)
    (m n : ℕ) (hn : 0 < n) (hp : (2 : ℝ)^m ≤ (1/t)^n)
    (hsq : (r/t)^2 ≤ (m : ℝ)/n) :
    r ≤ t * Real.sqrt (Real.logb 2 (1/t)) := by
  have hl := logb_lower_of_power (by norm_num : (1 : ℝ) < 2) (by positivity : 0 < 1/t) m n hn hp
  have hl0 : 0 ≤ Real.logb 2 (1/t) := le_trans (by positivity : (0 : ℝ) ≤ m/n) hl
  have hs := (Real.le_sqrt (div_nonneg hr ht.le) hl0).mpr (hsq.trans hl)
  have hm := mul_le_mul_of_nonneg_left hs ht.le
  simpa only [mul_div_cancel₀ r ht.ne'] using hm

end ChordBounds
lemma L_sixteenth : L (1/16) = 1/8 := by
  unfold L
  have hl : Real.logb 2 (1/((1 : ℝ)/16)) = 4 := by
    rw [show 1/((1 : ℝ)/16) = (2 : ℝ)^4 by norm_num, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num)]
    norm_num
  rw [hl]
  norm_num
lemma L_eighth_lower : (433:ℝ)/2000 ≤ L (1/8) := ChordBounds.logProfile_eighth
lemma L_three_sixteenths_lower : (2913:ℝ)/10000 ≤ L (3/16) :=
  ChordBounds.logProfile_three_sixteenths
lemma L_quarter_lower : (7071:ℝ)/20000 ≤ L (1/4) := ChordBounds.logProfile_quarter

noncomputable def chord (a b u v x : ℝ) : ℝ := ((b-x)*u+(x-a)*v)/(b-a)
lemma L_chord_lower {a b u v x : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1)
    (hb : b ∈ Set.Icc (0:ℝ) 1) (hab : a < b) (hx : x ∈ Set.Icc a b)
    (hu : u ≤ L a) (hv : v ≤ L b) : chord a b u v x ≤ L x := by
  have hp : 0 < b-a := sub_pos.mpr hab
  have hw0 : 0 ≤ (b-x)/(b-a) := div_nonneg (sub_nonneg.mpr hx.2) hp.le
  have hw1 : 0 ≤ (x-a)/(b-a) := div_nonneg (sub_nonneg.mpr hx.1) hp.le
  have hw : (b-x)/(b-a)+(x-a)/(b-a) = 1 := by field_simp; ring
  have h := L_concaveOn.2 ha hb hw0 hw1 hw
  have hpoint : ((b-x)/(b-a))*a+((x-a)/(b-a))*b=x := by field_simp; ring
  simp only [smul_eq_mul] at h
  rw [hpoint] at h
  have h0 := mul_le_mul_of_nonneg_left hu hw0
  have h1 := mul_le_mul_of_nonneg_left hv hw1
  unfold chord
  calc
    _ = (b-x)/(b-a)*u+(x-a)/(b-a)*v := by ring
    _ ≤ (b-x)/(b-a)*L a+(x-a)/(b-a)*L b := add_le_add h0 h1
    _ ≤ L x := h
lemma L_chord_0 {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) (1/16)) :
    chord 0 (1/16) 0 (1/8) x ≤ L x :=
  L_chord_lower (by norm_num) (by norm_num) (by norm_num) hx
    (by rw [L_zero]) (by rw [L_sixteenth])
lemma L_chord_1 {x : ℝ} (hx : x ∈ Set.Icc (1/16:ℝ) (1/8)) :
    chord (1/16) (1/8) (1/8) (433/2000) x ≤ L x :=
  L_chord_lower (by norm_num) (by norm_num) (by norm_num) hx
    (by rw [L_sixteenth]) L_eighth_lower
lemma L_chord_2 {x : ℝ} (hx : x ∈ Set.Icc (1/8:ℝ) (3/16)) :
    chord (1/8) (3/16) (433/2000) (2913/10000) x ≤ L x :=
  L_chord_lower (by norm_num) (by norm_num) (by norm_num) hx
    L_eighth_lower L_three_sixteenths_lower
lemma L_chord_3 {x : ℝ} (hx : x ∈ Set.Icc (3/16:ℝ) (1/4)) :
    chord (3/16) (1/4) (2913/10000) (7071/20000) x ≤ L x :=
  L_chord_lower (by norm_num) (by norm_num) (by norm_num) hx
    L_three_sixteenths_lower L_quarter_lower
end HammingCubeLog
