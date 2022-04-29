import number_theory.zsqrtd.basic
import data.complex.basic
import ring_theory.principal_ideal_domain
import number_theory.legendre_symbol.quadratic_reciprocity

open zsqrtd complex real

noncomputable theory

@[reducible] def gaussian_int2 : Type := zsqrtd (-2)

local notation `ℤ[√-2]` := gaussian_int2

namespace gaussian_int2

instance : has_repr ℤ[√-2] := ⟨λ x, "⟨" ++ repr x.re ++ ", " ++ repr x.im ++ "⟩"⟩

instance : comm_ring ℤ[√-2] := zsqrtd.comm_ring

section

/-- The embedding of the Gaussian integers into the complex numbers, as a ring homomorphism. -/
def to_complex : ℤ[√-2] →+* ℂ :=
begin
  refine zsqrtd.lift ⟨I*sqrt(2), _⟩,
  rw [← mul_assoc, ← mul_comm I (I * ↑(sqrt 2)), ← mul_assoc, I_mul_I],
  simp,
  rw ← sq,
  norm_cast,
  rw sq_sqrt,
  norm_num,
end

end

instance : has_coe (ℤ[√-2]) ℂ := ⟨to_complex⟩

lemma to_complex_def (x : ℤ[√-2]) : (x : ℂ) = x.re + x.im * I * sqrt(2) :=
begin
  rw [mul_assoc],
  refl,
end


lemma to_complex_def' (x y : ℤ) : ((⟨x, y⟩ : ℤ[√-2]) : ℂ) = x + y * I * sqrt(2) := by simp [to_complex_def]

lemma to_complex_def₂ (x : ℤ[√-2]) : (x : ℂ) = ⟨x.re, x.im * sqrt 2⟩ :=
by apply complex.ext; simp [to_complex_def]

@[simp] lemma to_real_re (x : ℤ[√-2]) : ((x.re : ℤ) : ℝ) = (x : ℂ).re :=
by simp [to_complex_def]

@[simp] lemma to_real_im (x : ℤ[√-2]) : ((x.im : ℤ) * sqrt 2 : ℝ) = (x : ℂ).im :=
by rw [to_complex_def₂]

@[simp] lemma to_complex_re (x y : ℤ) : ((⟨x, y⟩ : ℤ[√-2]) : ℂ).re = x := by simp [to_complex_def]

@[simp] lemma to_complex_im (x y : ℤ) : ((⟨x, y⟩ : ℤ[√-2]) : ℂ).im = y * sqrt 2 :=by simp [to_complex_def]

@[simp] lemma to_complex_add (x y : ℤ[√-2]) : ((x + y : ℤ[√-2]) : ℂ) = x + y := by exact to_complex.map_add _ _
@[simp] lemma to_complex_mul (x y : ℤ[√-2]) : ((x * y : ℤ[√-2]) : ℂ) = x * y := by exact to_complex.map_mul _ _
@[simp] lemma to_complex_one : ((1 : ℤ[√-2]) : ℂ) = 1 := by exact to_complex.map_one
@[simp] lemma to_complex_zero : ((0 : ℤ[√-2]) : ℂ) = 0 := by exact to_complex.map_zero
@[simp] lemma to_complex_neg (x : ℤ[√-2]) : ((-x : ℤ[√-2]) : ℂ) = -x := by exact to_complex.map_neg _
@[simp] lemma to_complex_sub (x y : ℤ[√-2]) : ((x - y : ℤ[√-2]) : ℂ) = x - y := by exact to_complex.map_sub _ _

@[simp] lemma to_complex_inj {x y : ℤ[√-2]} : (x : ℂ) = y ↔ x = y :=
 by cases x; cases y; simp [to_complex_def₂]

@[simp] lemma to_complex_eq_zero {x : ℤ[√-2]} : (x : ℂ) = 0 ↔ x = 0 :=
 by rw [← to_complex_zero, to_complex_inj]

@[simp] lemma nat_cast_real_norm (x : ℤ[√-2]) : (x.norm : ℝ)= (x : ℂ).norm_sq :=
begin
  rw [norm, norm_sq],
  simp,
  rw [← to_real_im],
  ring_nf,
  finish,
end


@[simp] lemma nat_cast_complex_norm (x : ℤ[√-2]) : (x.norm : ℂ) = (x : ℂ).norm_sq := 
begin
  cases x; rw [norm, norm_sq];
  norm_cast,
  simp,
  rw ← mul_comm (sqrt 2) ↑x_im,
  rw ← mul_assoc,
  rw ← mul_comm ↑x_im (sqrt 2),
  rw mul_assoc ↑x_im (sqrt 2) (sqrt 2),
  norm_num,
  ring_nf,
  finish,
end

lemma norm_nonneg (x : ℤ[√-2]) : 0 ≤ norm x := by refine norm_nonneg (by norm_num) _

@[simp] lemma norm_eq_zero {x : ℤ[√-2]} : norm x = 0 ↔ x = 0 := by rw [← @int.cast_inj ℝ _ _ _]; simp

lemma norm_pos {x : ℤ[√-2]} : 0 < norm x ↔ x ≠ 0 := by rw [lt_iff_le_and_ne, ne.def, eq_comm, norm_eq_zero]; simp [norm_nonneg]

@[simp] lemma coe_nat_abs_norm (x : ℤ[√-2]) : (x.norm.nat_abs : ℤ) =x.norm := by refine int.nat_abs_of_nonneg (norm_nonneg _)

@[simp] lemma nat_cast_nat_abs_norm {α : Type*} [ring α]
   (x : ℤ[√-2]) : (x.norm.nat_abs : α) = x.norm :=
 by rw [← int.cast_coe_nat, coe_nat_abs_norm]

 lemma nat_abs_norm_eq (x : ℤ[√-2]) : x.norm.nat_abs =
   x.re.nat_abs * x.re.nat_abs + 2 * x.im.nat_abs * x.im.nat_abs :=
  begin
    simp [norm],
    apply int.coe_nat_inj,
    nth_rewrite 1 [mul_assoc],
    nth_rewrite 0 [mul_assoc],
    simp,
    refine int.nat_abs_of_nonneg _,
    refine add_nonneg _ _,
    { exact mul_self_nonneg _ },
    { refine mul_nonneg _ _,
      { norm_num },
      { exact mul_self_nonneg _ } }
  end


protected def div (x y : ℤ[√-2]) : ℤ[√-2] :=
let n := (rat.of_int (norm y))⁻¹ in let c := y.conj in
⟨round (rat.of_int (x * c).re * n : ℚ),
round (rat.of_int (x * c).im * n : ℚ)⟩

instance : has_div ℤ[√-2] := ⟨gaussian_int2.div⟩

lemma div_def (x y : ℤ[√-2]) : x / y = ⟨round ((x * conj y).re / norm y : ℚ),
  round ((x * conj y).im / norm y : ℚ)⟩ :=
show zsqrtd.mk _ _ = _, by simp [rat.of_int_eq_mk, rat.mk_eq_div, div_eq_mul_inv]

lemma to_complex_div_re (x y : ℤ[√-2]) : ((x / y : ℤ[√-2]) : ℂ).re = round ((x / y : ℂ).re) :=
begin
  rw [div_def, ← @rat.round_cast ℝ _ _];
  simp [-rat.round_cast, mul_assoc, div_eq_mul_inv, mul_add, add_mul],
  congr' 1,
  congr' 1,
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc],
  congr' 1,
  rw [← to_real_im, ← to_real_im],
  rw [← mul_assoc, mul_comm (↑(x.im) * sqrt 2 * ↑(y.im)) (sqrt 2), ← mul_assoc, ← mul_assoc, mul_comm (sqrt 2 * ↑(x.im)) (sqrt 2), ← mul_assoc],
  simp,
end

lemma to_complex_div_im (x y : ℤ[√-2]) : ((x / y : ℤ[√-2]) : ℂ).im = round ((x / y : ℂ).im / sqrt 2) * sqrt 2 :=
begin
  rw [div_def, ← @rat.round_cast ℝ _ _, ← @rat.round_cast ℝ _ _];
  simp [-rat.round_cast, mul_assoc, div_eq_mul_inv, mul_add, add_mul],
  sorry
end

-- lemma norm_sq_le_norm_sq_of_re_le_of_im_le {x y : ℂ} (hre : |x.re| ≤ |y.re|)
--   (him : |x.im| ≤ |y.im|) : x.norm_sq ≤ y.norm_sq :=
-- by rw [norm_sq_apply, norm_sq_apply, ← _root_.abs_mul_self, _root_.abs_mul,
--   ← _root_.abs_mul_self y.re, _root_.abs_mul y.re,
--   ← _root_.abs_mul_self x.im, _root_.abs_mul x.im,
--   ← _root_.abs_mul_self y.im, _root_.abs_mul y.im]; exact
-- (add_le_add (mul_self_le_mul_self (abs_nonneg _) hre)
--   (mul_self_le_mul_self (abs_nonneg _) him))

lemma norm_sq_div_sub_div_lt_one (x y : ℤ[√-2]) :
  ((x / y : ℂ) - ((x / y : ℤ[√-2]) : ℂ)).norm_sq < 1 :=
begin
calc ((x / y : ℂ) - ((x / y : ℤ[√-2]) : ℂ)).norm_sq =
    ((x / y : ℂ).re - ((x / y : ℤ[√-2]) : ℂ).re +
    ((x / y : ℂ).im - ((x / y : ℤ[√-2]) : ℂ).im) * I : ℂ).norm_sq :
      congr_arg _ $ by apply complex.ext;
      simp
... = ((x / y : ℂ).re - ((x / y : ℤ[√-2]) : ℂ).re)^2 + ((x / y : ℂ).im - ((x / y : ℤ[√-2]) : ℂ).im)^2 :
      by norm_cast; rw norm_sq_add_mul_I
... <= 1/4 + 1/2 :
      _
... < 1 :
      by norm_num,

  have h1 : (1/4 : ℝ) = (1/2)^2, by norm_num,
  -- have h2 : (1/2 : ℝ) = 2*(1/4), by norm_num,
  refine add_le_add _ _,
  {
    rw to_complex_div_re,
    rw h1,
    apply sq_le_sq,
    -- nth_rewrite 1 [abs_of_pos],
    sorry
  },
  {
    sorry
  }
end

protected def mod (x y : ℤ[√-2]) : ℤ[√-2] := x - y * (x / y)

instance : has_mod ℤ[√-2] := ⟨gaussian_int2.mod⟩

lemma mod_def (x y : ℤ[√-2]) : x % y = x - y * (x / y) := rfl

-- lemma norm_mod_lt (x : ℤ[√-2]) {y : ℤ[√-2]} (hy : y ≠ 0) : (x % y).norm < y.norm :=
-- have (y : ℂ) ≠ 0, by rwa [ne.def, ← to_complex_zero, to_complex_inj],
-- (@int.cast_lt ℝ _ _ _ _).1 $
--   calc ↑(norm (x % y)) = (x - y * (x / y : ℤ[√-2]) : ℂ).norm_sq : by simp [mod_def]
--   ... = (y : ℂ).norm_sq * (((x / y) - (x / y : ℤ[√-2])) : ℂ).norm_sq :
--     by rw [← norm_sq_mul, mul_sub, mul_div_cancel' _ this]
--   ... < (y : ℂ).norm_sq * 1 : mul_lt_mul_of_pos_left (norm_sq_div_sub_div_lt_one _ _)
--     (norm_sq_pos.2 this)
--   ... = norm y : by simp


-- lemma nat_abs_norm_mod_lt (x : ℤ[√-2]) {y : ℤ[√-2]} (hy : y ≠ 0) :
--   (x % y).norm.nat_abs < y.norm.nat_abs :=
-- int.coe_nat_lt.1 (by simp [-int.coe_nat_lt, norm_mod_lt x hy])

-- lemma norm_le_norm_mul_left (x : ℤ[√-2]) {y : ℤ[√-2]} (hy : y ≠ 0) :
--   (norm x).nat_abs ≤ (norm (x * y)).nat_abs :=
-- by rw [norm_mul, int.nat_abs_mul];
--   exact le_mul_of_one_le_right (nat.zero_le _)
--     (int.coe_nat_le.1 (by rw [coe_nat_abs_norm]; exact int.add_one_le_of_lt (norm_pos.2 hy)))

-- instance : nontrivial ℤ[√-2] :=
-- ⟨⟨0, 1, dec_trivial⟩⟩

-- instance : euclidean_domain ℤ[√-2] :=
-- { quotient := (/),
--   remainder := (%),
--   quotient_zero := by { simp [div_def], refl },
--   quotient_mul_add_remainder_eq := λ _ _, by simp [mod_def],
--   r := _,
--   r_well_founded := measure_wf (int.nat_abs ∘ norm),
--   remainder_lt := nat_abs_norm_mod_lt,
--   mul_left_not_lt := λ a b hb0, not_lt_of_ge $ norm_le_norm_mul_left a hb0,
--   .. gaussian_int2.comm_ring,
--   .. gaussian_int2.nontrivial }

end gaussian_int2
