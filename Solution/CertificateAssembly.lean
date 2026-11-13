import Mathlib

namespace HammingCubeCertificateAssembly

noncomputable def assembled (L Q R : ℝ → ℝ) (t : ℝ) : ℝ :=
  if t ≤ 1/2 then max (L t) (Q t) else R t

noncomputable def twoPointOne (a b c d : ℝ) : ℝ :=
  Real.sqrt (d^2+b^2)+a-2*c

noncomputable def twoPointTwo (a b c d : ℝ) : ℝ :=
  d+(Real.sqrt 2-1)*b+a-2*c

/-- Every field is an analytic certificate to be supplied by a concrete profile.
The assembly theorem below does not assume any desired conclusion about `assembled`. -/
structure Certificates (L Q R : ℝ → ℝ) : Prop where
  L_zero : L 0 = 0
  Q_zero : Q 0 = 0
  R_one : R 1 = 0
  L_half : L (1/2) = 1/2
  Q_half : Q (1/2) = 1/2
  R_half : R (1/2) = 1/2
  L_nonneg : ∀ t ∈ Set.Icc 0 (1/2), 0 ≤ L t
  Q_nonneg : ∀ t ∈ Set.Icc 0 (1/2), 0 ≤ Q t
  R_nonneg : ∀ t ∈ Set.Icc (1/2) 1, 0 ≤ R t
  L_two_point : ∀ x y, 0 ≤ x → x ≤ y → y ≤ 1/2 →
    2*L ((x+y)/2) ≤ Real.sqrt ((y-x)^2+(L y)^2)+L x
  Q_two_point : ∀ x y, 0 ≤ x → x ≤ y → y ≤ 1/2 →
    2*Q ((x+y)/2) ≤ Real.sqrt ((y-x)^2+(Q y)^2)+Q x
  R_two_point : ∀ x y, 1/2 ≤ x → x ≤ y → y ≤ 1 →
    2*R ((x+y)/2) ≤ Real.sqrt ((y-x)^2+(R y)^2)+R x
  L_le_Q : ∀ t ∈ Set.Icc (1/4) (1/2), L t ≤ Q t
  LRQ : ∀ x y, x ∈ Set.Icc 0 (1/4) → y ∈ Set.Icc (1/2) 1 →
    (x+y)/2 ≤ 1/2 →
    0 ≤ max (twoPointOne (L x) (R y) (Q ((x+y)/2)) (y-x))
      (twoPointTwo (L x) (R y) (Q ((x+y)/2)) (y-x))
  LRR : ∀ x y, x ∈ Set.Icc 0 (1/4) → y ∈ Set.Icc (1/2) 1 →
    1/2 ≤ (x+y)/2 →
    0 ≤ max (twoPointOne (L x) (R y) (R ((x+y)/2)) (y-x))
      (twoPointTwo (L x) (R y) (R ((x+y)/2)) (y-x))
  QRQ : ∀ x y, x ∈ Set.Icc (1/4) (1/2) → y ∈ Set.Icc (1/2) 1 →
    (x+y)/2 ≤ 1/2 →
    2*Q ((x+y)/2) ≤ Real.sqrt ((y-x)^2+(R y)^2)+Q x
  QRR : ∀ x y, x ∈ Set.Icc (1/4) (1/2) → y ∈ Set.Icc (1/2) 1 →
    1/2 ≤ (x+y)/2 →
    2*R ((x+y)/2) ≤ Real.sqrt ((y-x)^2+(R y)^2)+Q x
  LR_symmetry : ∀ x ∈ Set.Icc 0 (1/4), 4*x*(1-x) ≤ L x+R (1-x)
  QR_symmetry : ∀ x ∈ Set.Icc (1/4) (1/2), 4*x*(1-x) ≤ Q x+R (1-x)

variable {L Q R : ℝ → ℝ}

lemma assembled_lower (t : ℝ) (ht : t ≤ 1/2) :
    assembled L Q R t = max (L t) (Q t) := if_pos ht

lemma assembled_zero (h : Certificates L Q R) : assembled L Q R 0 = 0 := by
  simp [assembled, h.L_zero, h.Q_zero]

lemma assembled_half (h : Certificates L Q R) : assembled L Q R (1/2) = 1/2 := by
  rw [assembled_lower (1/2) le_rfl, h.L_half, h.Q_half, max_self]

lemma assembled_one (h : Certificates L Q R) : assembled L Q R 1 = 0 := by
  rw [assembled, if_neg (by norm_num : ¬(1 : ℝ) ≤ 1/2)]
  exact h.R_one

lemma assembled_upper (h : Certificates L Q R) (t : ℝ) (ht : 1/2 ≤ t) :
    assembled L Q R t = R t := by
  rcases eq_or_lt_of_le ht with he | he
  · rw [← he, assembled_half h, h.R_half]
  · exact if_neg (not_le.mpr he)

lemma assembled_middle (h : Certificates L Q R) (t : ℝ)
    (ht : t ∈ Set.Icc (1/4) (1/2)) : assembled L Q R t = Q t := by
  rw [assembled_lower t ht.2, max_eq_right (h.L_le_Q t ht)]

lemma assembled_nonneg (h : Certificates L Q R) (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    0 ≤ assembled L Q R t := by
  by_cases hh : t ≤ 1/2
  · rw [assembled_lower t hh]
    exact (h.L_nonneg t ⟨ht.1,hh⟩).trans (le_max_left _ _)
  · rw [assembled_upper h t (le_of_not_ge hh)]
    exact h.R_nonneg t ⟨le_of_not_ge hh,ht.2⟩

lemma assembled_ge_L (t : ℝ) (ht : t ≤ 1/2) : L t ≤ assembled L Q R t := by
  rw [assembled_lower t ht]
  exact le_max_left _ _

lemma assembled_ge_Q (t : ℝ) (ht : t ≤ 1/2) : Q t ≤ assembled L Q R t := by
  rw [assembled_lower t ht]
  exact le_max_right _ _

lemma sqrt_sum_sq_mono {b b' d : ℝ} (hb : 0 ≤ b) (hbb : b ≤ b') :
    Real.sqrt (d^2+b^2) ≤ Real.sqrt (d^2+b'^2) := by
  apply Real.sqrt_le_sqrt
  have hsq := (sq_le_sq₀ hb (hb.trans hbb)).mpr hbb
  linarith

lemma assembled_lower_two_point (h : Certificates L Q R) (x y : ℝ)
    (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1/2) :
    2*assembled L Q R ((x+y)/2) ≤
      Real.sqrt ((y-x)^2+(assembled L Q R y)^2)+assembled L Q R x := by
  have hxhalf : x ≤ 1/2 := hxy.trans hy
  have hmhalf : (x+y)/2 ≤ 1/2 := by linarith
  rw [assembled_lower ((x+y)/2) hmhalf]
  have hL := h.L_two_point x y hx hxy hy
  have hQ := h.Q_two_point x y hx hxy hy
  have hsL := sqrt_sum_sq_mono (d := y-x) (h.L_nonneg y ⟨hx.trans hxy,hy⟩)
    (assembled_ge_L (L := L) (Q := Q) (R := R) y hy)
  have hsQ := sqrt_sum_sq_mono (d := y-x) (h.Q_nonneg y ⟨hx.trans hxy,hy⟩)
    (assembled_ge_Q (L := L) (Q := Q) (R := R) y hy)
  by_cases hc : L ((x+y)/2) ≤ Q ((x+y)/2)
  · rw [max_eq_right hc]
    linarith [assembled_ge_Q (L := L) (Q := Q) (R := R) x hxhalf]
  · rw [max_eq_left (le_of_not_ge hc)]
    linarith [assembled_ge_L (L := L) (Q := Q) (R := R) x hxhalf]

lemma max_twoPoint_mono_left {a a' b c d : ℝ} (ha : a ≤ a') :
    max (twoPointOne a b c d) (twoPointTwo a b c d) ≤
      max (twoPointOne a' b c d) (twoPointTwo a' b c d) := by
  apply max_le_max <;> dsimp [twoPointOne,twoPointTwo] <;> linarith

lemma assembled_two_point (h : Certificates L Q R) (x y : ℝ)
    (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) :
    0 ≤ max
      (Real.sqrt ((y-x)^2+(assembled L Q R y)^2)+assembled L Q R x-
        2*assembled L Q R ((x+y)/2))
      (y-x+(Real.sqrt 2-1)*assembled L Q R y+assembled L Q R x-
        2*assembled L Q R ((x+y)/2)) := by
  by_cases hyhalf : y ≤ 1/2
  · apply (le_max_left _ _).trans'
    linarith [assembled_lower_two_point h x y hx hxy hyhalf]
  have hyhalf' : 1/2 ≤ y := le_of_not_ge hyhalf
  by_cases hxhalf : 1/2 ≤ x
  · have hmhalf : 1/2 ≤ (x+y)/2 := by linarith
    rw [assembled_upper h y hyhalf',assembled_upper h x hxhalf,
      assembled_upper h ((x+y)/2) hmhalf]
    apply (le_max_left _ _).trans'
    linarith [h.R_two_point x y hxhalf hxy hy]
  have hxhalf' : x ≤ 1/2 := le_of_not_ge hxhalf
  rw [assembled_upper h y hyhalf']
  by_cases hmhalf : (x+y)/2 ≤ 1/2
  · have hmmid : (x+y)/2 ∈ Set.Icc (1/4) (1/2) := ⟨by linarith,hmhalf⟩
    rw [assembled_middle h ((x+y)/2) hmmid]
    by_cases hxquarter : x ≤ 1/4
    · exact (h.LRQ x y ⟨hx,hxquarter⟩ ⟨hyhalf',hy⟩ hmhalf).trans
        (max_twoPoint_mono_left (assembled_ge_L (L := L) (Q := Q) (R := R) x hxhalf'))
    · have hxmid : x ∈ Set.Icc (1/4) (1/2) := ⟨le_of_not_ge hxquarter,hxhalf'⟩
      rw [assembled_middle h x hxmid]
      apply (le_max_left _ _).trans'
      linarith [h.QRQ x y hxmid ⟨hyhalf',hy⟩ hmhalf]
  · have hmhalf' : 1/2 ≤ (x+y)/2 := le_of_not_ge hmhalf
    rw [assembled_upper h ((x+y)/2) hmhalf']
    by_cases hxquarter : x ≤ 1/4
    · exact (h.LRR x y ⟨hx,hxquarter⟩ ⟨hyhalf',hy⟩ hmhalf').trans
        (max_twoPoint_mono_left (assembled_ge_L (L := L) (Q := Q) (R := R) x hxhalf'))
    · have hxmid : x ∈ Set.Icc (1/4) (1/2) := ⟨le_of_not_ge hxquarter,hxhalf'⟩
      rw [assembled_middle h x hxmid]
      apply (le_max_left _ _).trans'
      linarith [h.QRR x y hxmid ⟨hyhalf',hy⟩ hmhalf']

lemma assembled_symmetry_half (h : Certificates L Q R) (x : ℝ)
    (hx : x ∈ Set.Icc 0 (1/2)) :
    4*x*(1-x) ≤ assembled L Q R x+assembled L Q R (1-x) := by
  rw [assembled_upper h (1-x) (by linarith [hx.2])]
  by_cases hxq : x ≤ 1/4
  · have hh := h.LR_symmetry x ⟨hx.1,hxq⟩
    linarith [assembled_ge_L (L := L) (Q := Q) (R := R) x hx.2]
  · have hxm : x ∈ Set.Icc (1/4) (1/2) := ⟨le_of_not_ge hxq,hx.2⟩
    rw [assembled_middle h x hxm]
    exact h.QR_symmetry x hxm

lemma assembled_symmetry (h : Certificates L Q R) (x : ℝ)
    (hx : x ∈ Set.Icc 0 1) :
    4*x*(1-x) ≤ assembled L Q R x+assembled L Q R (1-x) := by
  by_cases hxh : x ≤ 1/2
  · exact assembled_symmetry_half h x ⟨hx.1,hxh⟩
  · have hc : 1-x ∈ Set.Icc 0 (1/2) := by constructor <;> linarith [hx.2]
    have hh := assembled_symmetry_half h (1-x) hc
    have he : 1-(1-x)=x := by ring
    rw [he] at hh
    nlinarith

end HammingCubeCertificateAssembly
