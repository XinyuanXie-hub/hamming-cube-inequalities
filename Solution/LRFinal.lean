import Solution.ChordBounds
import Solution.LRAssemble
import Solution.AlternativeProfile

set_option maxHeartbeats 0
namespace HammingCubeLRFinal
open HammingCubeLR
open HammingCubeLog (L chord L_chord_0 L_chord_1 L_chord_2 L_chord_3)
lemma interval_param {a b t : ℝ} (ht : t ∈ Set.Icc a b) :
    ∃ v : ℝ, v ∈ Set.Icc 0 1 ∧ a+(b-a)*v=t := by
  rcases eq_or_lt_of_le (le_trans ht.1 ht.2) with he | hp
  · refine ⟨0,by norm_num,?_⟩
    have ha : a=t := le_antisymm ht.1 (by linarith [ht.2])
    simp [ha]
  · refine ⟨(t-a)/(b-a),⟨div_nonneg (sub_nonneg.mpr ht.1) (sub_pos.mpr hp).le,
      (div_le_one (sub_pos.mpr hp)).2 (by linarith [ht.2])⟩,?_⟩
    field_simp
    ring
lemma x_param (i x : ℝ) (hx : x ∈ Set.Icc (i/16) ((i+1)/16)) :
    ∃ u : ℝ, u ∈ Set.Icc 0 1 ∧ (i+u)/16=x := by
  refine ⟨16*x-i,⟨by linarith [hx.1],by linarith [hx.2]⟩,?_⟩
  ring
lemma C0_le_L {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) (1/16)) : C0 x ≤ L x := by
  convert L_chord_0 hx using 1
  dsimp [C0,chord]
  ring
lemma C1_le_L {x : ℝ} (hx : x ∈ Set.Icc (1/16:ℝ) (1/8)) : C1 x ≤ L x := by
  convert L_chord_1 hx using 1
  dsimp [C1,chord]
  ring
lemma C2_le_L {x : ℝ} (hx : x ∈ Set.Icc (1/8:ℝ) (3/16)) : C2 x ≤ L x := by
  convert L_chord_2 hx using 1
  dsimp [C2,chord]
  ring
lemma C3_le_L {x : ℝ} (hx : x ∈ Set.Icc (3/16:ℝ) (1/4)) : C3 x ≤ L x := by
  convert L_chord_3 hx using 1
  dsimp [C3,chord]
  ring

lemma LR0Qa_actual (x y : ℝ) (hx : x ∈ Set.Icc (0:ℝ) (1/16))
    (hy : y ∈ Set.Icc (1/2) (1/2+x)) :
    2*Q ((x+y)/2) ≤ max (Real.sqrt ((y-x)^2+(R y)^2))
      (y-x+(Real.sqrt 2-1)*R y)+L x := by
  obtain ⟨u,hu,hxu⟩ := x_param 0 x (by convert hx using 1 <;> norm_num)
  obtain ⟨v,hv,hyv⟩ := interval_param hy
  have heX : XLR0Qa u=x := by exact hxu
  have heY : YLR0Qa u v=y := by
    dsimp only [YLR0Qa]
    rw [heX]
    convert hyv using 1 <;> ring
  have h := LR0Qa_region u v hu hv
  rw [heX,heY] at h
  exact h.trans (add_le_add_right (C0_le_L hx) _)

lemma LR0Qb_actual (x y : ℝ) (hx : x ∈ Set.Icc (0:ℝ) (1/16))
    (hy : y ∈ Set.Icc (1/2+x) (1-x)) :
    2*Q ((x+y)/2) ≤ max (Real.sqrt ((y-x)^2+(R y)^2))
      (y-x+(Real.sqrt 2-1)*R y)+L x := by
  obtain ⟨u,hu,hxu⟩ := x_param 0 x (by convert hx using 1 <;> norm_num)
  obtain ⟨v,hv,hyv⟩ := interval_param hy
  have heX : XLR0Qb u=x := by exact hxu
  have heY : YLR0Qb u v=y := by
    dsimp only [YLR0Qb]
    rw [heX]
    convert hyv using 1 <;> ring
  have h := LR0Qb_region u v hu hv
  rw [heX,heY] at h
  exact h.trans (add_le_add_right (C0_le_L hx) _)

lemma LR0R_actual (x y : ℝ) (hx : x ∈ Set.Icc (0:ℝ) (1/16))
    (hy : y ∈ Set.Icc (1-x) (1)) :
    2*R ((x+y)/2) ≤ max (Real.sqrt ((y-x)^2+(R y)^2))
      (y-x+(Real.sqrt 2-1)*R y)+L x := by
  obtain ⟨u,hu,hxu⟩ := x_param 0 x (by convert hx using 1 <;> norm_num)
  obtain ⟨v,hv,hyv⟩ := interval_param hy
  have heX : XLR0R u=x := by exact hxu
  have heY : YLR0R u v=y := by
    dsimp only [YLR0R]
    rw [heX]
    convert hyv using 1 <;> ring
  have h := LR0R_region u v hu hv
  rw [heX,heY] at h
  exact h.trans (add_le_add_right (C0_le_L hx) _)

lemma LR1Q_actual (x y : ℝ) (hx : x ∈ Set.Icc (1/16:ℝ) (1/8))
    (hy : y ∈ Set.Icc (1/2) (1-x)) :
    2*Q ((x+y)/2) ≤ max (Real.sqrt ((y-x)^2+(R y)^2))
      (y-x+(Real.sqrt 2-1)*R y)+L x := by
  obtain ⟨u,hu,hxu⟩ := x_param 1 x (by convert hx using 1 <;> norm_num)
  have hyrect : y ∈ Set.Icc (1/2 : ℝ) (15/16) :=
    ⟨hy.1, by linarith [hx.1, hy.2]⟩
  obtain ⟨v,hv,hyv⟩ := interval_param hyrect
  have heX : XLR1Q u=x := by exact hxu
  have heY : YLR1Q u v=y := by
    dsimp only [YLR1Q]
    convert hyv using 1
    ring
  have h := LR1Q_region u v hu hv
  rw [heX,heY] at h
  exact h.trans (add_le_add_right (C1_le_L hx) _)

lemma LR1R_actual (x y : ℝ) (hx : x ∈ Set.Icc (1/16:ℝ) (1/8))
    (hy : y ∈ Set.Icc (1-x) (1)) :
    2*R ((x+y)/2) ≤ max (Real.sqrt ((y-x)^2+(R y)^2))
      (y-x+(Real.sqrt 2-1)*R y)+L x := by
  obtain ⟨u,hu,hxu⟩ := x_param 1 x (by convert hx using 1 <;> norm_num)
  obtain ⟨v,hv,hyv⟩ := interval_param hy
  have heX : XLR1R u=x := by exact hxu
  have heY : YLR1R u v=y := by
    dsimp only [YLR1R]
    rw [heX]
    convert hyv using 1 <;> ring
  have h := LR1R_region u v hu hv
  rw [heX,heY] at h
  exact h.trans (add_le_add_right (C1_le_L hx) _)

lemma LR2Q_actual (x y : ℝ) (hx : x ∈ Set.Icc (1/8:ℝ) (3/16))
    (hy : y ∈ Set.Icc (1/2) (1-x)) :
    2*Q ((x+y)/2) ≤ max (Real.sqrt ((y-x)^2+(R y)^2))
      (y-x+(Real.sqrt 2-1)*R y)+L x := by
  obtain ⟨u,hu,hxu⟩ := x_param 2 x (by convert hx using 1 <;> norm_num)
  obtain ⟨v,hv,hyv⟩ := interval_param hy
  have heX : XLR2Q u=x := by exact hxu
  have heY : YLR2Q u v=y := by
    dsimp only [YLR2Q]
    rw [heX]
    convert hyv using 1 <;> ring
  have h := LR2Q_region u v hu hv
  rw [heX,heY] at h
  exact h.trans (add_le_add_right (C2_le_L hx) _)

lemma LR2R_actual (x y : ℝ) (hx : x ∈ Set.Icc (1/8:ℝ) (3/16))
    (hy : y ∈ Set.Icc (1-x) (1)) :
    2*R ((x+y)/2) ≤ max (Real.sqrt ((y-x)^2+(R y)^2))
      (y-x+(Real.sqrt 2-1)*R y)+L x := by
  obtain ⟨u,hu,hxu⟩ := x_param 2 x (by convert hx using 1 <;> norm_num)
  obtain ⟨v,hv,hyv⟩ := interval_param hy
  have heX : XLR2R u=x := by exact hxu
  have heY : YLR2R u v=y := by
    dsimp only [YLR2R]
    rw [heX]
    convert hyv using 1 <;> ring
  have h := LR2R_region u v hu hv
  rw [heX,heY] at h
  exact h.trans (add_le_add_right (C2_le_L hx) _)

lemma LR3Q_actual (x y : ℝ) (hx : x ∈ Set.Icc (3/16:ℝ) (1/4))
    (hy : y ∈ Set.Icc (1/2) (1-x)) :
    2*Q ((x+y)/2) ≤ max (Real.sqrt ((y-x)^2+(R y)^2))
      (y-x+(Real.sqrt 2-1)*R y)+L x := by
  obtain ⟨u,hu,hxu⟩ := x_param 3 x (by convert hx using 1 <;> norm_num)
  have hyrect : y ∈ Set.Icc (1/2 : ℝ) (13/16) :=
    ⟨hy.1, by linarith [hx.1, hy.2]⟩
  obtain ⟨v,hv,hyv⟩ := interval_param hyrect
  have heX : XLR3Q u=x := by exact hxu
  have heY : YLR3Q u v=y := by
    dsimp only [YLR3Q]
    convert hyv using 1
    ring
  have h := LR3Q_region u v hu hv
  rw [heX,heY] at h
  exact h.trans (add_le_add_right (C3_le_L hx) _)

lemma LR3R_actual (x y : ℝ) (hx : x ∈ Set.Icc (3/16:ℝ) (1/4))
    (hy : y ∈ Set.Icc (1-x) (1)) :
    2*R ((x+y)/2) ≤ max (Real.sqrt ((y-x)^2+(R y)^2))
      (y-x+(Real.sqrt 2-1)*R y)+L x := by
  obtain ⟨u,hu,hxu⟩ := x_param 3 x (by convert hx using 1 <;> norm_num)
  obtain ⟨v,hv,hyv⟩ := interval_param hy
  have heX : XLR3R u=x := by exact hxu
  have heY : YLR3R u v=y := by
    dsimp only [YLR3R]
    rw [heX]
    convert hyv using 1 <;> ring
  have h := LR3R_region u v hu hv
  rw [heX,heY] at h
  exact h.trans (add_le_add_right (C3_le_L hx) _)

theorem LRQ_bound (x y : ℝ) (hx : x ∈ Set.Icc 0 (1/4))
    (hy : y ∈ Set.Icc (1/2) 1) (hm : (x+y)/2 ≤ 1/2) :
    2*AlternativeProfile.Q ((x+y)/2) ≤ max (Real.sqrt ((y-x)^2+(AlternativeProfile.R y)^2))
      (y-x+(Real.sqrt 2-1)*AlternativeProfile.R y)+L x := by
  change 2*Q ((x+y)/2) ≤ max (Real.sqrt ((y-x)^2+(R y)^2))
    (y-x+(Real.sqrt 2-1)*R y)+L x
  by_cases h0 : x ≤ 1/16
  · by_cases hs : y ≤ 1/2+x
    · exact LR0Qa_actual x y ⟨hx.1,h0⟩ ⟨hy.1,hs⟩
    · exact LR0Qb_actual x y ⟨hx.1,h0⟩ ⟨by linarith,by linarith⟩
  · by_cases h1 : x ≤ 1/8
    · exact LR1Q_actual x y ⟨by linarith,h1⟩ ⟨hy.1,by linarith⟩
    · by_cases h2 : x ≤ 3/16
      · exact LR2Q_actual x y ⟨by linarith,h2⟩ ⟨hy.1,by linarith⟩
      · exact LR3Q_actual x y ⟨by linarith,hx.2⟩ ⟨hy.1,by linarith⟩

theorem LRR_bound (x y : ℝ) (hx : x ∈ Set.Icc 0 (1/4))
    (hy : y ∈ Set.Icc (1/2) 1) (hm : 1/2 ≤ (x+y)/2) :
    2*AlternativeProfile.R ((x+y)/2) ≤ max (Real.sqrt ((y-x)^2+(AlternativeProfile.R y)^2))
      (y-x+(Real.sqrt 2-1)*AlternativeProfile.R y)+L x := by
  change 2*R ((x+y)/2) ≤ max (Real.sqrt ((y-x)^2+(R y)^2))
    (y-x+(Real.sqrt 2-1)*R y)+L x
  have hy' : y ∈ Set.Icc (1-x) 1 := ⟨by linarith,hy.2⟩
  by_cases h0 : x ≤ 1/16
  · exact LR0R_actual x y ⟨hx.1,h0⟩ hy'
  · by_cases h1 : x ≤ 1/8
    · exact LR1R_actual x y ⟨by linarith,h1⟩ hy'
    · by_cases h2 : x ≤ 3/16
      · exact LR2R_actual x y ⟨by linarith,h2⟩ hy'
      · exact LR3R_actual x y ⟨by linarith,hx.2⟩ hy'
#print axioms LRQ_bound
#print axioms LRR_bound
end HammingCubeLRFinal
