import data.rat.order
import number_theory.zsqrtd.basic
import algebra.order.archimedean


lemma debut (x : ℚ) : ∃ (y : ℤ), |x - y| ≤ 1/2 :=
begin
  sorry,/- 
  use round x,
  rw round,
  rw abs_sub_le_iff,
  have h := int.floor_le (x + 1/2),
  split,
  {
    rw sub_le,
    rw le_trans ((x - 1 / 2) ≤ (↑⌊x + 1 / 2⌋)) h,
  } -/
end