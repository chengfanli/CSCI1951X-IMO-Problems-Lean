import LoVe.LoVelib
import AutograderLib
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Basic

namespace LoVe
namespace PROJECT


variable {f : ℝ → ℝ}
variable {a : ℝ} (h_a_pos : a > 0)
variable (h_f_eq : ∀ (x : ℝ), f (x + a) = (1 / 2) + Real.sqrt (f x - (f x) ^ 2))

variable (h_nonneg_pre : ∀ (x : ℝ), f x - (f x) ^ 2 ≥ 0)
variable (h_lt : ∀ (x : ℝ), 0 ≤ f x - 1 / 2)

lemma f_periodic : ∀ (x : ℝ), f (x + (a + a)) = f x := by
  intro x
  have h_fxa_ge : f (x + a) ≥ 1 / 2 := by
    have h_sqrt_nonneg : Real.sqrt (f x - (f x) ^ 2) ≥ 0 := Real.sqrt_nonneg _
    linarith [h_f_eq x, h_sqrt_nonneg]

  have h1 : f (x + a) * (1 - f (x + a)) = (1 / 4) - (f x - (f x) ^ 2) := by
    have h_fxa : f (x + a) = (1 / 2) + Real.sqrt (f x - (f x) ^ 2) := by
      apply h_f_eq x
    have h00 : f (x + a) * (1 - f (x + a)) = (1 / 4) - (f x - (f x) ^ 2) := by
      calc
        f (x + a) * (1 - f (x + a)) = ((1 / 2) + Real.sqrt (f x - (f x) ^ 2)) * (1 - ((1 / 2) + Real.sqrt (f x - (f x) ^ 2))) := by rw [h_fxa]
        _ = ((1 / 2) + Real.sqrt (f x - (f x) ^ 2)) * ((1 - 1 / 2) - Real.sqrt (f x - (f x) ^ 2)) := by ring
        _ = ((1 / 2) + Real.sqrt (f x - (f x) ^ 2)) * ((1 / 2) - Real.sqrt (f x - (f x) ^ 2)) := by ring
        _ = (1 / 2 + Real.sqrt (f x - (f x) ^ 2)) * (1 / 2 - Real.sqrt (f x - (f x) ^ 2)) := by exact rfl
        _ = (1 / 4) - (Real.sqrt (f x - (f x) ^ 2)) ^ 2 := by ring
        _ = (1 / 4) - (f x - (f x) ^ 2) := by
          have h_sqrt_nonneg :0 ≤ f x - (f x) ^ 2 := by exact h_nonneg_pre x
          have h11 : (Real.sqrt (f x - (f x) ^ 2)) ^ 2 = (f x - (f x) ^ 2) := by
            exact Real.sq_sqrt h_sqrt_nonneg
          exact congrArg (HSub.hSub (1 / 4)) h11
    exact h00

  have h_f2a_0 : f (x + a + a) = (1 / 2) + Real.sqrt (f (x + a) - (f (x + a)) ^ 2) := by
    exact h_f_eq (x + a)
  have h_f2a_1 : f (x + (a + a)) = f (x + a + a) := by ring_nf

  have h_f2a : f (x + (a + a)) = (1 / 2) + Real.sqrt (f (x + a) - (f (x + a)) ^ 2) := by
    rw [h_f2a_1]
    exact h_f_eq (x + a)

  have h11 : f (x + (a + a)) = f x := by
    calc
      f (x + (a + a)) = (1 / 2) + Real.sqrt (f (x + a) - (f (x + a)) ^ 2) := by rw [h_f2a]
      _ = (1 / 2) + Real.sqrt (f (x + a) * (1 - f (x + a))) := by ring_nf
      _ = (1 / 2) + Real.sqrt ((1 / 4) - (f x - (f x) ^ 2)) := by rw [h1]
      _ = (1 / 2) + Real.sqrt ((1 / 4) - (f x - (f x) ^ 2)) := by exact rfl
      _ = (1 / 2) + Real.sqrt ((1 / 4) - f x + (f x) ^ 2) := by ring_nf
      _ = (1 / 2) + Real.sqrt ((f x - 1 / 2) ^ 2) := by ring_nf
      _ = (1 / 2) + |f x - (1 / 2)| := by
        rw [Real.sqrt_sq]
        have h_nonneg : 0 ≤ f x - (1 / 2) := h_lt x
        {rw [abs_of_nonneg h_nonneg]}
        {exact h_lt x}
      _ = (1 / 2) + (f x - 1 / 2) := by
        have h_nonneg : 0 ≤ f x - (1 / 2) := h_lt x
        rw [abs_of_nonneg h_nonneg]
      _ = 1 / 2 + f x - 1 / 2 := by ring
      _ = f x := by exact add_sub_cancel_left (1 / 2) (f x)

  exact h11

theorem exists_periodic_b : ∃ b > 0, ∀ (x : ℝ), f (x + b) = f x := by
  use a + a
  apply And.intro
  {
    exact Right.add_pos' h_a_pos h_a_pos
  }
  {
    exact fun x => f_periodic h_f_eq h_nonneg_pre h_lt x
  }




end PROJECT end LoVe
