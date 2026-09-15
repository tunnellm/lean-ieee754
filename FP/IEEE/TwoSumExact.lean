import FP.IEEE.RoundingBounds

/-! Exact reconstruction in the classical six-operation binary TwoSum algorithm. -/
noncomputable section
namespace FP.IEEE.Format

private theorem sub_sum_exact_nonneg (F : Format) {x y s : ℝ}
    (hx : F.Representable x) (hy : F.Representable y) (hs : F.Representable s)
    (hseq : s = F.roundFinite (x+y)) (hx0 : 0 ≤ x)
    (hlo : -x ≤ y) (hhi : y ≤ x) : F.Representable (s-x) := by
  have hlat := F.add_min_lattice hx hy
  by_cases hy0 : 0 ≤ y
  · have hxs : x ≤ s := hseq ▸ F.le_roundFinite hx (by linarith)
    have hsx : s ≤ 2*x := hseq ▸ F.roundFinite_le_double hx (by linarith)
    exact F.sterbenz hs hx (by linarith) (by linarith)
  · by_cases hc : x/2 ≤ -y
    · have hr := F.sterbenz hx (F.representable_neg hy) hc (by linarith)
      have he : s = x+y := by rw [hseq, F.roundFinite_exact (by simpa using hr)]
      simpa [he] using hy
    · have hxs : x/2 ≤ s := hseq ▸ F.half_le_roundFinite hx hx0 (by linarith) hlat
      have hsx : s ≤ x := hseq ▸ F.roundFinite_le hx (by linarith)
      exact F.sterbenz hs hx (by linarith) (by linarith)

/-- When the first input dominates, the virtual second addend is exact. -/
theorem twoSum_bvirt_exact_of_abs_le (F : Format) {x y s : ℝ}
    (hx : F.Representable x) (hy : F.Representable y) (hs : F.Representable s)
    (hseq : s = F.roundFinite (x+y)) (hmag : |y| ≤ |x|) :
    F.Representable (s-x) := by
  by_cases hx0 : 0 ≤ x
  · rw [abs_of_nonneg hx0, abs_le] at hmag
    exact sub_sum_exact_nonneg F hx hy hs hseq hx0 hmag.1 hmag.2
  · have hm : -(-x) ≤ -y ∧ -y ≤ -x := by
      rw [abs_of_nonpos (le_of_not_ge hx0), abs_le] at hmag
      constructor <;> linarith
    have hr := sub_sum_exact_nonneg F (F.representable_neg hx) (F.representable_neg hy)
      (F.representable_neg hs)
      (show -s = F.roundFinite (-x + -y) by
        rw [← neg_add, F.roundFinite_neg, hseq])
      (by linarith) hm.1 hm.2
    simpa [sub_eq_add_neg, add_comm] using F.representable_neg hr

private theorem reconstruct_of_exact_sum (F : Format) {x y s v : ℝ}
    (hx : F.Representable x) (hy : F.Representable y)
    (hseq : s = x+y) (hveq : v = F.roundFinite (s-x)) :
    F.Representable (s-v) ∧ F.Representable (y-v) := by
  have hv : v = y := by rw [hveq, hseq, add_sub_cancel_left, F.roundFinite_exact hy]
  simp only [hv, sub_self, hseq, add_sub_cancel_right]
  exact ⟨hx,F.representable_zero⟩

private theorem reconstructions_nonneg_right (F : Format) {x y s v : ℝ}
    (hx : F.Representable x) (hy : F.Representable y)
    (hs : F.Representable s) (hv : F.Representable v)
    (hseq : s = F.roundFinite (x+y)) (hveq : v = F.roundFinite (s-x))
    (hy0 : 0 ≤ y) (hmag : |x| ≤ y) :
    F.Representable (s-v) ∧ F.Representable (y-v) := by
  have hxy : -y ≤ x ∧ x ≤ y := abs_le.mp hmag
  have hlat := F.add_min_lattice hx hy
  have hvlat := F.sub_min_lattice hs hx
  by_cases hx0 : 0 ≤ x
  · have hys : y ≤ s := hseq ▸ F.le_roundFinite hy (by linarith)
    have hs2y : s ≤ 2*y := hseq ▸ F.roundFinite_le_double hy (by linarith)
    have h2xs : 2*x ≤ s := hseq ▸ F.double_le_roundFinite hx (by linarith)
    have hs0 : 0 ≤ s := by linarith
    have hvlo : s/2 ≤ v := hveq ▸ F.half_le_roundFinite hs hs0 (by linarith) hvlat
    have hvhi : v ≤ s := hveq ▸ F.roundFinite_le hs (by linarith)
    have hvylo : y/2 ≤ v := hveq ▸ F.half_le_roundFinite hy hy0 (by linarith) hvlat
    have hvyhi : v ≤ 2*y := hveq ▸ F.roundFinite_le_double hy (by linarith)
    exact ⟨F.sterbenz hs hv hvlo (by linarith), F.sterbenz hy hv hvylo hvyhi⟩
  · by_cases hc : y/2 ≤ -x
    · have hr := F.sterbenz hy (F.representable_neg hx) hc (by linarith)
      have he : s = x+y := by
        rw [hseq, F.roundFinite_exact (by simpa [add_comm] using hr)]
      exact reconstruct_of_exact_sum F hx hy he hveq
    · have hslo : y/2 ≤ s := hseq ▸ F.half_le_roundFinite hy hy0 (by linarith) hlat
      have hshi : s ≤ y := hseq ▸ F.roundFinite_le hy (by linarith)
      have hs0 : 0 ≤ s := by linarith
      have hvlo : s ≤ v := hveq ▸ F.le_roundFinite hs (by linarith)
      have hvhi : v ≤ 2*s := hveq ▸ F.roundFinite_le_double hs (by linarith)
      exact ⟨F.sterbenz hs hv (by linarith) hvhi,
        F.sterbenz hy hv (by linarith) (by linarith)⟩

/-- Both remaining TwoSum reconstruction expressions are representable.
Only the inputs, initial sum, and virtual second addend must be finite.
No input ordering, reconstruction certificate, or normal-range assumption is used. -/
theorem twoSum_reconstructions (F : Format) {x y s v : ℝ}
    (hx : F.Representable x) (hy : F.Representable y)
    (hs : F.Representable s) (hv : F.Representable v)
    (hseq : s = F.roundFinite (x+y)) (hveq : v = F.roundFinite (s-x)) :
    F.Representable (s-v) ∧ F.Representable (y-v) := by
  rcases le_total |y| |x| with hmag | hmag
  · have hr := F.twoSum_bvirt_exact_of_abs_le hx hy hs hseq hmag
    have he : v = s-x := hveq.trans (F.roundFinite_exact hr)
    constructor
    · simpa [he] using hx
    · have herr := F.roundFinite_add_residual_representable hx hy
      rw [← hseq] at herr
      convert herr using 1
      rw [he]
      ring
  · by_cases hy0 : 0 ≤ y
    · exact reconstructions_nonneg_right F hx hy hs hv hseq hveq hy0
        (by simpa [abs_of_nonneg hy0] using hmag)
    · have hm : |-x| ≤ -y := by simpa [abs_of_nonpos (le_of_not_ge hy0)] using hmag
      have hr := reconstructions_nonneg_right F
        (F.representable_neg hx) (F.representable_neg hy)
        (F.representable_neg hs) (F.representable_neg hv)
        (show -s = F.roundFinite (-x + -y) by rw [← neg_add, F.roundFinite_neg, hseq])
        (show -v = F.roundFinite (-s - -x) by
          rw [show -s - -x = -(s-x) by ring, F.roundFinite_neg, hveq])
        (by linarith) hm
      constructor
      · simpa [sub_eq_add_neg, add_comm] using F.representable_neg hr.1
      · simpa [sub_eq_add_neg, add_comm] using F.representable_neg hr.2

theorem twoSum_avirt_representable (F : Format) {x y s v : ℝ}
    (hx : F.Representable x) (hy : F.Representable y)
    (hs : F.Representable s) (hv : F.Representable v)
    (hseq : s = F.roundFinite (x+y)) (hveq : v = F.roundFinite (s-x)) :
    F.Representable (s-v) := (F.twoSum_reconstructions hx hy hs hv hseq hveq).1

theorem twoSum_bround_representable (F : Format) {x y s v : ℝ}
    (hx : F.Representable x) (hy : F.Representable y)
    (hs : F.Representable s) (hv : F.Representable v)
    (hseq : s = F.roundFinite (x+y)) (hveq : v = F.roundFinite (s-x)) :
    F.Representable (y-v) := (F.twoSum_reconstructions hx hy hs hv hseq hveq).2

end FP.IEEE.Format
