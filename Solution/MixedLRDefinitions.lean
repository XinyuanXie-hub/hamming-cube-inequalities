import Mathlib
set_option maxRecDepth 10000
set_option maxHeartbeats 0
noncomputable section
namespace HammingCubeLR

def Q (x : ℝ) : ℝ := (2/3:ℝ)*x*(1-x)*(4*Real.sqrt 2-3+4*(3-2*Real.sqrt 2)*x)
def R (x : ℝ) : ℝ :=
  let z := 2*x-1
  1/2+2037*z/25000-9759*z^2/20000+123*z^3/1250-471*z^4/1250+
    24189*z^5/50000-29891*z^6/100000
def C0 (x : ℝ) : ℝ := 2*x+(0)
def C1 (x : ℝ) : ℝ := (183/125:ℝ)*x+((67/2000:ℝ))
def C2 (x : ℝ) : ℝ := (748/625:ℝ)*x+((669/10000:ℝ))
def C3 (x : ℝ) : ℝ := (249/250:ℝ)*x+((2091/20000:ℝ))
end HammingCubeLR
