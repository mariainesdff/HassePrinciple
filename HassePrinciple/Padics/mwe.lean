import Mathlib

variable {p : ℕ} [Fact (Nat.Prime p)]

example {v : (ℚ_[p])ˣ} {x y z : ℤ_[p]} (hnewsol : (z : ℚ_[p]) ^ 2 - p * (x : ℚ_[p]) ^ 2 -
v * (y : ℚ_[p]) ^ 2 = 0) (this : ¬ IsUnit z) : ‖y‖ < 1 := by
  have hvy'_int : ‖v * (y : ℚ_[p]) ^ 2‖ ≤ 1 := by sorry -- already proved, but omitted here
  have vy_sq_eq : (v : ℚ_[p])*(y : ℚ_[p]) ^ 2 = (z : ℚ_[p]) ^ 2
      - (p : ℚ_[p]) * (x : ℚ_[p]) ^ 2 := by
    rw [sub_eq_zero] at hnewsol
    rw [← hnewsol]
  rw [PadicInt.not_isUnit_iff, PadicInt.norm_lt_one_iff_dvd] at this
  have vy'_sq_norm_ne_one : ‖(v : ℚ_[p])*(y : ℚ_[p]) ^ 2‖ < 1 := by
    rw [vy_sq_eq]
    rw [dvd_def] at this
    sorry
  sorry


--  hy'_norm_ne_one {v : (ℚ_[p])ˣ} {x y z : ℚ_[p]}
--     (hnontriv : (x, y, z) ≠ (0, 0, 0)) (hsol : z ^ 2 - p * x ^ 2 - v * y ^ 2 = 0) :
--     ‖y'‖ < 1 := by
--       have hvy'_int : ‖v * (y' : ℚ_[p]) ^ 2‖ ≤ 1 := by sorry -- already proved
--       have vy'_sq_eq : (v : ℚ_[p])*(y' : ℚ_[p]) ^ 2 = (z' : ℚ_[p]) ^ 2
--       - (p : ℚ_[p]) * (x' : ℚ_[p]) ^ 2 := by sorry -- already proved
--       have vy'_sq_norm_ne_one : ‖(v : ℚ_[p])*(y' : ℚ_[p]) ^ 2‖ < 1 := by
--         rw [vy'_sq_eq]
--         rw [dvd_def] at this
--         sorry -- want help here
--       sorry
