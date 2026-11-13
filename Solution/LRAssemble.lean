import Solution.LR0Qa
import Solution.LR0Qb
import Solution.LR0R
import Solution.LR1Q
import Solution.LR1R
import Solution.LR2Q
import Solution.LR2R
import Solution.LR3Q
import Solution.LR3R
set_option maxHeartbeats 0
namespace HammingCubeLR

theorem LR0Qa_region (u v : ℝ) (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1) :
    2*Q ((XLR0Qa u+YLR0Qa u v)/2) ≤
      max (Real.sqrt ((YLR0Qa u v-XLR0Qa u)^2+(R (YLR0Qa u v))^2)) (YLR0Qa u v-XLR0Qa u+(Real.sqrt 2-1)*R (YLR0Qa u v)) + C0 (XLR0Qa u) := by
  rcases hu with ⟨hu0,hu1⟩
  rcases hv with ⟨hv0,hv1⟩
  have h := LR0Qa_leaf0 u v ⟨by linarith,by linarith⟩ ⟨by linarith,by linarith⟩
  have hs := Real.le_sqrt_of_sq_le (show (2*Q ((XLR0Qa u+YLR0Qa u v)/2)-C0 (XLR0Qa u))^2 ≤ (YLR0Qa u v-XLR0Qa u)^2+(R (YLR0Qa u v))^2 by linarith)
  have hm := le_max_left (Real.sqrt ((YLR0Qa u v-XLR0Qa u)^2+(R (YLR0Qa u v))^2)) (YLR0Qa u v-XLR0Qa u+(Real.sqrt 2-1)*R (YLR0Qa u v))
  linarith

theorem LR0Qb_region (u v : ℝ) (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1) :
    2*Q ((XLR0Qb u+YLR0Qb u v)/2) ≤
      max (Real.sqrt ((YLR0Qb u v-XLR0Qb u)^2+(R (YLR0Qb u v))^2)) (YLR0Qb u v-XLR0Qb u+(Real.sqrt 2-1)*R (YLR0Qb u v)) + C0 (XLR0Qb u) := by
  rcases hu with ⟨hu0,hu1⟩
  rcases hv with ⟨hv0,hv1⟩
  have h := LR0Qb_leaf0 u v ⟨by linarith,by linarith⟩ ⟨by linarith,by linarith⟩
  have hm := le_max_right (Real.sqrt ((YLR0Qb u v-XLR0Qb u)^2+(R (YLR0Qb u v))^2)) (YLR0Qb u v-XLR0Qb u+(Real.sqrt 2-1)*R (YLR0Qb u v))
  linarith

theorem LR0R_region (u v : ℝ) (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1) :
    2*R ((XLR0R u+YLR0R u v)/2) ≤
      max (Real.sqrt ((YLR0R u v-XLR0R u)^2+(R (YLR0R u v))^2)) (YLR0R u v-XLR0R u+(Real.sqrt 2-1)*R (YLR0R u v)) + C0 (XLR0R u) := by
  rcases hu with ⟨hu0,hu1⟩
  rcases hv with ⟨hv0,hv1⟩
  have h := LR0R_leaf0 u v ⟨by linarith,by linarith⟩ ⟨by linarith,by linarith⟩
  have hm := le_max_right (Real.sqrt ((YLR0R u v-XLR0R u)^2+(R (YLR0R u v))^2)) (YLR0R u v-XLR0R u+(Real.sqrt 2-1)*R (YLR0R u v))
  linarith

theorem LR1Q_region (u v : ℝ) (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1) :
    2*Q ((XLR1Q u+YLR1Q u v)/2) ≤ max (Real.sqrt ((YLR1Q u v-XLR1Q u)^2+(R (YLR1Q u v))^2)) (YLR1Q u v-XLR1Q u+(Real.sqrt 2-1)*R (YLR1Q u v))+C1 (XLR1Q u) := by
  rcases hu with ⟨hu0,hu1⟩
  rcases hv with ⟨hv0,hv1⟩
  by_cases h0 : v ≤ (1/2:ℝ)
  · by_cases h1 : u ≤ (1/2:ℝ)
    · by_cases h2 : v ≤ (1/4:ℝ)
      · have h := LR1Q_leaf0 u v ⟨by linarith,by linarith⟩ ⟨by linarith,by linarith⟩
        have hs := Real.le_sqrt_of_sq_le (show (2*Q ((XLR1Q u+YLR1Q u v)/2)-C1 (XLR1Q u))^2 ≤ (YLR1Q u v-XLR1Q u)^2+(R (YLR1Q u v))^2 by linarith)
        have hm := le_max_left (Real.sqrt ((YLR1Q u v-XLR1Q u)^2+(R (YLR1Q u v))^2)) (YLR1Q u v-XLR1Q u+(Real.sqrt 2-1)*R (YLR1Q u v))
        linarith
      · have h := LR1Q_leaf1 u v ⟨by linarith,by linarith⟩ ⟨by linarith,by linarith⟩
        have hm := le_max_right (Real.sqrt ((YLR1Q u v-XLR1Q u)^2+(R (YLR1Q u v))^2)) (YLR1Q u v-XLR1Q u+(Real.sqrt 2-1)*R (YLR1Q u v))
        linarith
    · by_cases h2 : v ≤ (1/4:ℝ)
      · have h := LR1Q_leaf2 u v ⟨by linarith,by linarith⟩ ⟨by linarith,by linarith⟩
        have hs := Real.le_sqrt_of_sq_le (show (2*Q ((XLR1Q u+YLR1Q u v)/2)-C1 (XLR1Q u))^2 ≤ (YLR1Q u v-XLR1Q u)^2+(R (YLR1Q u v))^2 by linarith)
        have hm := le_max_left (Real.sqrt ((YLR1Q u v-XLR1Q u)^2+(R (YLR1Q u v))^2)) (YLR1Q u v-XLR1Q u+(Real.sqrt 2-1)*R (YLR1Q u v))
        linarith
      · have h := LR1Q_leaf3 u v ⟨by linarith,by linarith⟩ ⟨by linarith,by linarith⟩
        have hm := le_max_right (Real.sqrt ((YLR1Q u v-XLR1Q u)^2+(R (YLR1Q u v))^2)) (YLR1Q u v-XLR1Q u+(Real.sqrt 2-1)*R (YLR1Q u v))
        linarith
  · have h := LR1Q_leaf4 u v ⟨by linarith,by linarith⟩ ⟨by linarith,by linarith⟩
    have hm := le_max_right (Real.sqrt ((YLR1Q u v-XLR1Q u)^2+(R (YLR1Q u v))^2)) (YLR1Q u v-XLR1Q u+(Real.sqrt 2-1)*R (YLR1Q u v))
    linarith

theorem LR1R_region (u v : ℝ) (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1) :
    2*R ((XLR1R u+YLR1R u v)/2) ≤
      max (Real.sqrt ((YLR1R u v-XLR1R u)^2+(R (YLR1R u v))^2)) (YLR1R u v-XLR1R u+(Real.sqrt 2-1)*R (YLR1R u v)) + C1 (XLR1R u) := by
  rcases hu with ⟨hu0,hu1⟩
  rcases hv with ⟨hv0,hv1⟩
  have h := LR1R_leaf0 u v ⟨by linarith,by linarith⟩ ⟨by linarith,by linarith⟩
  have hm := le_max_right (Real.sqrt ((YLR1R u v-XLR1R u)^2+(R (YLR1R u v))^2)) (YLR1R u v-XLR1R u+(Real.sqrt 2-1)*R (YLR1R u v))
  linarith

theorem LR2Q_region (u v : ℝ) (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1) :
    2*Q ((XLR2Q u+YLR2Q u v)/2) ≤
      max (Real.sqrt ((YLR2Q u v-XLR2Q u)^2+(R (YLR2Q u v))^2)) (YLR2Q u v-XLR2Q u+(Real.sqrt 2-1)*R (YLR2Q u v)) + C2 (XLR2Q u) := by
  rcases hu with ⟨hu0,hu1⟩
  rcases hv with ⟨hv0,hv1⟩
  by_cases h0 : u ≤ (1/2:ℝ)
  · by_cases h1 : v ≤ (1/2:ℝ)
    · have h := LR2Q_leaf0 u v ⟨by linarith,by linarith⟩ ⟨by linarith,by linarith⟩
      have hs := Real.le_sqrt_of_sq_le (show (2*Q ((XLR2Q u+YLR2Q u v)/2)-C2 (XLR2Q u))^2 ≤ (YLR2Q u v-XLR2Q u)^2+(R (YLR2Q u v))^2 by linarith)
      have hm := le_max_left (Real.sqrt ((YLR2Q u v-XLR2Q u)^2+(R (YLR2Q u v))^2)) (YLR2Q u v-XLR2Q u+(Real.sqrt 2-1)*R (YLR2Q u v))
      linarith
    · have h := LR2Q_leaf1 u v ⟨by linarith,by linarith⟩ ⟨by linarith,by linarith⟩
      have hm := le_max_right (Real.sqrt ((YLR2Q u v-XLR2Q u)^2+(R (YLR2Q u v))^2)) (YLR2Q u v-XLR2Q u+(Real.sqrt 2-1)*R (YLR2Q u v))
      linarith
  · by_cases h1 : v ≤ (1/2:ℝ)
    · have h := LR2Q_leaf2 u v ⟨by linarith,by linarith⟩ ⟨by linarith,by linarith⟩
      have hs := Real.le_sqrt_of_sq_le (show (2*Q ((XLR2Q u+YLR2Q u v)/2)-C2 (XLR2Q u))^2 ≤ (YLR2Q u v-XLR2Q u)^2+(R (YLR2Q u v))^2 by linarith)
      have hm := le_max_left (Real.sqrt ((YLR2Q u v-XLR2Q u)^2+(R (YLR2Q u v))^2)) (YLR2Q u v-XLR2Q u+(Real.sqrt 2-1)*R (YLR2Q u v))
      linarith
    · have h := LR2Q_leaf3 u v ⟨by linarith,by linarith⟩ ⟨by linarith,by linarith⟩
      have hm := le_max_right (Real.sqrt ((YLR2Q u v-XLR2Q u)^2+(R (YLR2Q u v))^2)) (YLR2Q u v-XLR2Q u+(Real.sqrt 2-1)*R (YLR2Q u v))
      linarith

theorem LR2R_region (u v : ℝ) (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1) :
    2*R ((XLR2R u+YLR2R u v)/2) ≤
      max (Real.sqrt ((YLR2R u v-XLR2R u)^2+(R (YLR2R u v))^2)) (YLR2R u v-XLR2R u+(Real.sqrt 2-1)*R (YLR2R u v)) + C2 (XLR2R u) := by
  rcases hu with ⟨hu0,hu1⟩
  rcases hv with ⟨hv0,hv1⟩
  have h := LR2R_leaf0 u v ⟨by linarith,by linarith⟩ ⟨by linarith,by linarith⟩
  have hm := le_max_right (Real.sqrt ((YLR2R u v-XLR2R u)^2+(R (YLR2R u v))^2)) (YLR2R u v-XLR2R u+(Real.sqrt 2-1)*R (YLR2R u v))
  linarith

theorem LR3Q_region (u v : ℝ) (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1) :
    2*Q ((XLR3Q u+YLR3Q u v)/2) ≤ max (Real.sqrt ((YLR3Q u v-XLR3Q u)^2+(R (YLR3Q u v))^2)) (YLR3Q u v-XLR3Q u+(Real.sqrt 2-1)*R (YLR3Q u v))+C3 (XLR3Q u) := by
  rcases hu with ⟨hu0,hu1⟩
  rcases hv with ⟨hv0,hv1⟩
  by_cases h0 : v ≤ (1/2:ℝ)
  · by_cases h1 : u ≤ (1/2:ℝ)
    · have h := LR3Q_leaf0 u v ⟨by linarith,by linarith⟩ ⟨by linarith,by linarith⟩
      have hs := Real.le_sqrt_of_sq_le (show (2*Q ((XLR3Q u+YLR3Q u v)/2)-C3 (XLR3Q u))^2 ≤ (YLR3Q u v-XLR3Q u)^2+(R (YLR3Q u v))^2 by linarith)
      have hm := le_max_left (Real.sqrt ((YLR3Q u v-XLR3Q u)^2+(R (YLR3Q u v))^2)) (YLR3Q u v-XLR3Q u+(Real.sqrt 2-1)*R (YLR3Q u v))
      linarith
    · have h := LR3Q_leaf1 u v ⟨by linarith,by linarith⟩ ⟨by linarith,by linarith⟩
      have hs := Real.le_sqrt_of_sq_le (show (2*Q ((XLR3Q u+YLR3Q u v)/2)-C3 (XLR3Q u))^2 ≤ (YLR3Q u v-XLR3Q u)^2+(R (YLR3Q u v))^2 by linarith)
      have hm := le_max_left (Real.sqrt ((YLR3Q u v-XLR3Q u)^2+(R (YLR3Q u v))^2)) (YLR3Q u v-XLR3Q u+(Real.sqrt 2-1)*R (YLR3Q u v))
      linarith
  · by_cases h1 : u ≤ (1/2:ℝ)
    · have h := LR3Q_leaf2 u v ⟨by linarith,by linarith⟩ ⟨by linarith,by linarith⟩
      have hs := Real.le_sqrt_of_sq_le (show (2*Q ((XLR3Q u+YLR3Q u v)/2)-C3 (XLR3Q u))^2 ≤ (YLR3Q u v-XLR3Q u)^2+(R (YLR3Q u v))^2 by linarith)
      have hm := le_max_left (Real.sqrt ((YLR3Q u v-XLR3Q u)^2+(R (YLR3Q u v))^2)) (YLR3Q u v-XLR3Q u+(Real.sqrt 2-1)*R (YLR3Q u v))
      linarith
    · have h := LR3Q_leaf3 u v ⟨by linarith,by linarith⟩ ⟨by linarith,by linarith⟩
      have hs := Real.le_sqrt_of_sq_le (show (2*Q ((XLR3Q u+YLR3Q u v)/2)-C3 (XLR3Q u))^2 ≤ (YLR3Q u v-XLR3Q u)^2+(R (YLR3Q u v))^2 by linarith)
      have hm := le_max_left (Real.sqrt ((YLR3Q u v-XLR3Q u)^2+(R (YLR3Q u v))^2)) (YLR3Q u v-XLR3Q u+(Real.sqrt 2-1)*R (YLR3Q u v))
      linarith

theorem LR3R_region (u v : ℝ) (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1) :
    2*R ((XLR3R u+YLR3R u v)/2) ≤
      max (Real.sqrt ((YLR3R u v-XLR3R u)^2+(R (YLR3R u v))^2)) (YLR3R u v-XLR3R u+(Real.sqrt 2-1)*R (YLR3R u v)) + C3 (XLR3R u) := by
  rcases hu with ⟨hu0,hu1⟩
  rcases hv with ⟨hv0,hv1⟩
  have h := LR3R_leaf0 u v ⟨by linarith,by linarith⟩ ⟨by linarith,by linarith⟩
  have hm := le_max_right (Real.sqrt ((YLR3R u v-XLR3R u)^2+(R (YLR3R u v))^2)) (YLR3R u v-XLR3R u+(Real.sqrt 2-1)*R (YLR3R u v))
  linarith

end HammingCubeLR
