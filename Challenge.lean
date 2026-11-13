import Mathlib

open scoped BigOperators

namespace HammingCube

abbrev Cube (n : ℕ) := Fin n → Bool

def flip {n : ℕ} (x : Cube n) (i : Fin n) : Cube n :=
  Function.update x i (!x i)

noncomputable def avg {n : ℕ} (f : Cube n → ℝ) : ℝ :=
  (∑ x, f x) / (2 : ℝ) ^ n

noncomputable def density {n : ℕ} (A : Finset (Cube n)) : ℝ :=
  (A.card : ℝ) / (2 : ℝ) ^ n

/-- Theorem 1.1, equation (1.1); the expression at density zero is zero. -/
theorem theorem_1_1 (n : ℕ) (hn : 1 ≤ n) (A : Finset (Cube n))
    (hA : density A ≤ 1 / 2) :
    let h := fun x : Cube n =>
      if x ∈ A then ((Finset.univ.filter (fun i => flip x i ∉ A)).card : ℝ) else 0
    density A * Real.sqrt (Real.logb 2 (1 / density A)) ≤
      avg (fun x => Real.sqrt (h x)) := by
  sorry

/-- Theorem 1.2 (Kahn–Park): each edge from A to B is counted once. -/
theorem theorem_1_2 (n : ℕ) (hn : 1 ≤ n) (A B W : Finset (Cube n))
    (hAB : Disjoint A B) (hAW : Disjoint A W) (hBW : Disjoint B W)
    (hcover : A ∪ B ∪ W = Finset.univ) (hA : density A = 1 / 2) :
    let edgeMeasure :=
      (∑ x ∈ A, ((Finset.univ.filter (fun i => flip x i ∈ B)).card : ℝ)) /
        (2 : ℝ) ^ n
    (1 : ℝ) / 2 ≤ edgeMeasure + Real.sqrt (n : ℝ) * density W := by
  sorry

/-- Theorem 1.3, including equality for the indicator of either half-cube. -/
theorem theorem_1_3 (n : ℕ) (hn : 1 ≤ n) (f : Cube n → ℝ)
    (hf : ∀ x, f x = 0 ∨ f x = 1) :
    let gradient := fun x : Cube n =>
      Real.sqrt (∑ i : Fin n, ((f x - f (flip x i)) / 2) ^ 2)
    let deviation := avg (fun x => |f x - avg f|)
    deviation ≤ avg gradient ∧
      (∀ (i : Fin n) (b : Bool),
        (∀ x, f x = if x i = b then 1 else 0) → deviation = avg gradient) := by
  sorry

end HammingCube
