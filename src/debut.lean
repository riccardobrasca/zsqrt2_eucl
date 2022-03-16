import data.rat.order
import number_theory.zsqrtd.basic
import algebra.order.archimedean

lemma debut (x : ℚ) : ∃ (y : ℤ), |x - y| ≤ 1/2 :=
begin
  sorry
end

open zsqrtd

example (n : ℤ) (x y : ℤ√(-2)) : conj (0 : ℤ√(-2)) = 0 :=
begin
  simp,
end