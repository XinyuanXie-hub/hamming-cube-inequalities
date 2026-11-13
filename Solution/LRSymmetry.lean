import Mathlib
namespace PolynomialLRSym
noncomputable def L (x : ℝ) : ℝ := x*Real.sqrt (Real.logb 2 (1/x))
noncomputable def R (x : ℝ) : ℝ :=
  let z := 2*x-1
  1/2 + 2037*z/25000 - 9759*z^2/20000 + 123*z^3/1250 -
    471*z^4/1250 + 24189*z^5/50000 - 29891*z^6/100000
lemma L_lower_linear (x : ℝ) (hx : x ∈ Set.Icc 0 (1/4)) :
    Real.sqrt 2*x ≤ L x := by
  by_cases hz : x=0
  · simp [L,hz]
  have hp : 0<x := lt_of_le_of_ne hx.1 (Ne.symm hz)
  have h4 : (4:ℝ) ≤ 1/x := (le_div_iff₀ hp).mpr (by linarith [hx.2])
  have hh := Real.logb_le_logb_of_le (show (1:ℝ)<2 by norm_num)
    (show (0:ℝ)<4 by norm_num) h4
  have hlog : Real.logb 2 (4:ℝ)=2 := by
    rw [show (4:ℝ)=2^(2:ℕ) by norm_num,Real.logb_pow,Real.logb_self_eq_one (by norm_num)]
    norm_num
  rw [hlog] at hh
  have hs := Real.sqrt_le_sqrt hh
  unfold L
  nlinarith
lemma R_linear_symmetry (x : ℝ) (hx : x ∈ Set.Icc 0 (1/4)) :
    4*x*(1-x) ≤ Real.sqrt 2*x+R (1-x) := by
  have hs2 : (Real.sqrt (2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hs := Real.sqrt_nonneg (2:ℝ)
  have hlo : (7/5:ℝ) ≤ Real.sqrt 2 := by nlinarith
  have hx0 : 0≤4*x := by linarith [hx.1]
  have hx1 : 0≤1-4*x := by linarith [hx.2]
  have h1 : 0≤((-25951/100000:ℝ)+(1/4:ℝ)*Real.sqrt 2) := by linarith
  have h2 : 0≤((-3931/2500:ℝ)+(5/4:ℝ)*Real.sqrt 2) := by linarith
  have h3 : 0≤((-67517/20000:ℝ)+(5/2:ℝ)*Real.sqrt 2) := by linarith
  have h4 : 0≤((-1101071/320000:ℝ)+(5/2:ℝ)*Real.sqrt 2) := by linarith
  have h5 : 0≤((-1364213/800000:ℝ)+(5/4:ℝ)*Real.sqrt 2) := by linarith
  have h6 : 0≤((-2125119/6400000:ℝ)+(1/4:ℝ)*Real.sqrt 2) := by linarith
  have heq : Real.sqrt 2*x+R (1-x)-4*x*(1-x)=
    ((-25951/100000:ℝ)+(1/4:ℝ)*Real.sqrt 2)*(4*x)^1*(1-4*x)^5 +
    ((-3931/2500:ℝ)+(5/4:ℝ)*Real.sqrt 2)*(4*x)^2*(1-4*x)^4 +
    ((-67517/20000:ℝ)+(5/2:ℝ)*Real.sqrt 2)*(4*x)^3*(1-4*x)^3 +
    ((-1101071/320000:ℝ)+(5/2:ℝ)*Real.sqrt 2)*(4*x)^4*(1-4*x)^2 +
    ((-1364213/800000:ℝ)+(5/4:ℝ)*Real.sqrt 2)*(4*x)^5*(1-4*x)^1 +
    ((-2125119/6400000:ℝ)+(1/4:ℝ)*Real.sqrt 2)*(4*x)^6*(1-4*x)^0 := by unfold R; ring
  have hh : 0≤Real.sqrt 2*x+R (1-x)-4*x*(1-x) := by rw [heq]; positivity
  linarith
lemma LR_symmetry (x : ℝ) (hx : x ∈ Set.Icc 0 (1/4)) :
    4*x*(1-x) ≤ L x+R (1-x) := by
  have h1 := L_lower_linear x hx
  have h2 := R_linear_symmetry x hx
  linarith
end PolynomialLRSym
