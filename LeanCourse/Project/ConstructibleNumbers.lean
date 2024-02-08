import LeanCourse.Common
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Order.AbsoluteValue
import Mathlib.Algebra.Field.Basic
import Mathlib.FieldTheory.Subfield
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Algebra.GroupPower.Basic
open BigOperators Function Ideal Polynomial Classical Matrix
noncomputable section
set_option linter.unusedVariables false
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)
set_option maxHeartbeats 20000000 -- at some point some strategies didnt work anymore without increasing the maxHeartbeats

-- Everything proven, except for the fact that the constructible numbers are the smallest subfield of ℂ closed under square roots (but i have proven that they are closed under square roots!)

structure circle_with_radius := -- Own definition of a circle, because only unit circle is defined in mathlib
(center : ℂ)
(radius : ℝ)

def circle_with_radius.points (c : circle_with_radius) : Set ℂ :=
  {z | Complex.abs (z - c.center) = c.radius}

 structure line_through_two_points :=
(z₁ z₂ : ℂ)

def line_through_two_points.points (l : line_through_two_points) : Set ℂ := --lines defined through affine combination
  { (t : ℂ) * l.z₁ + (1-t) * l.z₂ | (t : ℝ) }

lemma line_through_two_points_beginn_in_points (l : line_through_two_points) : l.z₁ ∈ l.points := by{
  use 1
  simp
}

lemma line_through_two_points_end_in_points (l : line_through_two_points) : l.z₂ ∈ l.points := by{
  use 0
  simp
}

def constructible_circles (M : Set ℂ) : Set circle_with_radius :=
  { c | ∃ p a b , c = {center := p, radius := Complex.abs (a - b : ℂ)} ∧ p ∈ M ∧ a ∈ M ∧ b ∈ M }

def constructible_lines (M : Set ℂ) : Set line_through_two_points :=
  {l | ∃ z₁ z₂ , l = {z₁ := z₁, z₂ := z₂} ∧ z₁ ∈ M ∧ z₂ ∈ M}

def line_line_intersection (l₁ l₂ : line_through_two_points) : Set ℂ :=
  { z | z ∈ l₁.points ∩ l₂.points }

def line_circle_intersection (l : line_through_two_points) (c : circle_with_radius) : Set ℂ :=
  { z | z ∈ l.points ∩ c.points }

def circle_circle_intersection (c₁ c₂ : circle_with_radius)  : Set ℂ :=
  { z | z ∈ c₁.points ∩ c₂.points }
-- Just there to abbrieviate the next definition
def intersections (M : Set ℂ) (lines : Set line_through_two_points) (circles : Set circle_with_radius) : Set ℂ :=
  let line_intersections := ⋃(l₁ ∈ lines) (l₂ ∈ lines) (h: l₁.points ≠ l₂.points), line_line_intersection l₁ l₂ --note that for lines the .points condition is importatn but not für circles, because they are uniquely defined by their center and radius
  let line_circle_intersections := ⋃(l ∈ lines) (c ∈ circles), line_circle_intersection l c
  let circle_intersections := ⋃(c₁ ∈ circles) (c₂ ∈ circles) (h: c₁ ≠ c₂) , circle_circle_intersection c₁ c₂
  line_intersections ∪ line_circle_intersections ∪ circle_intersections

def constructible_numbers_rec (M: Set ℂ) (h0 : 0 ∈M) (h1 : 1 ∈ M ) : Nat → Set ℂ --recursively define the constructible numbers until the n-th step
  | 0   => M
  | n+1 => constructible_numbers_rec M (h0) (h1) n ∪ intersections (constructible_numbers_rec M h0 h1 n) (constructible_lines (constructible_numbers_rec M (h0) (h1) n)) (constructible_circles (constructible_numbers_rec M (h0) (h1) n))
-- useful lemma
lemma constructible_numbers_rec_element_of (M: Set ℂ) (h0 : 0 ∈M) (h1 : 1 ∈ M ) (n : ℕ) (m : ℕ ) (hm : m ≥ n) (z : ℂ) (hz : z ∈ constructible_numbers_rec M (h0) (h1) n) : z ∈ constructible_numbers_rec M (h0) (h1) (m) := by{
  induction m
  case zero =>
    have h1: n = 0 := Nat.eq_zero_of_le_zero hm
    rw [h1] at hz
    exact hz
  case succ m hmi =>
    by_cases hc: n ≤ m
    · left
      exact hmi hc
    · push_neg at hc
      have h2 : n = m + 1 := by linarith
      rw [h2] at hz
      exact hz
}

lemma constructible_numbers_rec_zero (M: Set ℂ) (h0 : 0 ∈M) (h1 : 1 ∈ M ) : 0 ∈ constructible_numbers_rec M (h0) (h1) 0 := by{
  exact h0
}

lemma constructible_numbers_rec_one (M: Set ℂ) (h0 : 0 ∈M) (h1 : 1 ∈ M ) : 1 ∈ constructible_numbers_rec M (h0) (h1) 0 := by{
  exact h1
}
-- useful lemma
@[simp] lemma constructible_numbers_mono (M: Set ℂ) (h0 : 0 ∈ M) (h1: 1 ∈ M) (n m : ℕ) (h : n ≤ m) : constructible_numbers_rec M (h0) (h1) n ⊆ constructible_numbers_rec M (h0) (h1) m := by{
  intro z hz
  induction m
  case zero =>
    have h1: n = 0 := Nat.eq_zero_of_le_zero h
    rw [h1] at hz
    exact hz
  case succ m hm =>
    by_cases hc: n ≤ m
    · left
      exact hm hc
    · push_neg at hc
      have h2 : n = m + 1 := by linarith
      rw [h2] at hz
      assumption
}
-- define the constructible numbers as the union of the constructible numbers at each step
def constructible_numbers (M : Set ℂ) (h0: 0 ∈ M) (h1: 1 ∈ M) : Set ℂ :=
    ⋃(n : ℕ), constructible_numbers_rec M (h0) (h1) n
-- useful lemma
lemma subset_constructible_numbers (M : Set ℂ) (h0: 0 ∈ M ) (h1 : 1 ∈ M): M ⊆ constructible_numbers M (h0) (h1) := by{
  intro z hz
  have h1 : constructible_numbers_rec M (h0) (h1) 0 ⊆ constructible_numbers M (h0) (h1) := by{
     apply Set.subset_sUnion_of_mem
     use 0
  }
  exact h1 hz
}

lemma constructible_numbers_rec_subset_constructible_numbers (M : Set ℂ) (h0: 0 ∈ M ) (h1 : 1 ∈ M) (n : ℕ) : constructible_numbers_rec M (h0) (h1) n ⊆ constructible_numbers M (h0) (h1) := by{
  apply Set.subset_sUnion_of_mem
  use n
}
-- following 3 lemma are extremly useful
-- i didn't find a way to minimize the amount used "max"
lemma element_circle_circle_intersection_constructible (M : Set ℂ) (h0: 0 ∈ M) (h1: 1 ∈ M) (c₁ c₂ : circle_with_radius) (hc₁: c₁ ∈ constructible_circles (constructible_numbers M h0 h1)) (hc₂: c₂ ∈ constructible_circles (constructible_numbers M h0 h1)) (hcc: c₁ ≠ c₂ ) (z : ℂ) (hz : z ∈ circle_circle_intersection c₁ c₂) : z ∈ constructible_numbers M (h0) (h1) := by{
  obtain⟨p1, a1, b1, hc1, hp1, ha1, hb1⟩ := hc₁
  obtain⟨p2, a2, b2, hc2, hp2, ha2, hb2⟩ := hc₂
  obtain⟨ M1, hf1, hM1⟩ := ha1
  obtain⟨ m1, hm1⟩ := hf1
  obtain⟨ M2, hf2, hM2⟩ := ha2
  obtain⟨ m2, hm2⟩ := hf2
  obtain ⟨M3, hf3, hM3⟩ := hb1
  obtain ⟨m3, hm3⟩ := hf3
  obtain ⟨M4, hf4, hM4⟩ := hb2
  obtain ⟨m4, hm4⟩ := hf4
  obtain ⟨M5, hf5, hM5⟩ := hp1
  obtain ⟨m5, hm5⟩ := hf5
  obtain ⟨M6, hf6, hM6⟩ := hp2
  obtain ⟨m6, hm6⟩ := hf6
  have : circle_circle_intersection c₁ c₂ ⊆ constructible_numbers_rec M (h0) (h1) (max (max (max (max (max m1 m2) m3) m4) m5) m6 + 1) := by{
    intros z hz
    unfold constructible_numbers_rec
    simp
    right
    unfold intersections
    right
    have hc1' : c₁ ∈ constructible_circles (constructible_numbers_rec M (h0) (h1) (max (max (max (max (max m1 m2) m3) m4) m5) m6)) := by{
      use p1
      use a1
      use b1
      simp
      constructor
      ·  exact hc1
      · constructor
        · have hm5': m5 ≤ max (max (max (max (max m1 m2) m3) m4) m5) m6 := by{
            simp
          }
          have hp1 : p1 ∈ constructible_numbers_rec M (h0) (h1) m5 := by{
            aesop
          }
          exact constructible_numbers_rec_element_of M h0 h1 m5 (max (max (max (max (max m1 m2) m3) m4) m5) m6) hm5' p1 hp1
        · constructor
          · have hm1': m1 ≤ max (max (max (max (max m1 m2) m3) m4) m5) m6 := by{
            simp
            }
            have ha1 : a1 ∈ constructible_numbers_rec M (h0) (h1) m1 := by{
              aesop
            }
            exact constructible_numbers_rec_element_of M h0 h1 m1 (max (max (max (max (max m1 m2) m3) m4) m5) m6) hm1' a1 ha1
          · have hm3': m3 ≤ max (max (max (max (max m1 m2) m3) m4) m5) m6 := by{
            simp
            }
            have hb1 : b1 ∈ constructible_numbers_rec M (h0) (h1) m3 := by{
              aesop
            }
            exact constructible_numbers_rec_element_of M h0 h1 m3 (max (max (max (max (max m1 m2) m3) m4) m5) m6) hm3' b1 hb1
    }
    have hc2' : c₂ ∈ constructible_circles (constructible_numbers_rec M (h0) (h1) (max (max (max (max (max m1 m2) m3) m4) m5) m6)) := by{
      use p2
      use a2
      use b2
      simp
      constructor
      ·  exact hc2
      · constructor
        · have hm6': m6 ≤ max (max (max (max (max m1 m2) m3) m4) m5) m6 := by{
            simp
          }
          have hp2 : p2 ∈ constructible_numbers_rec M (h0) (h1) m6 := by{
            aesop
          }
          exact constructible_numbers_rec_element_of M h0 h1 m6 (max (max (max (max (max m1 m2) m3) m4) m5) m6) hm6' p2 hp2
        · constructor
          · have hm2': m2 ≤ max (max (max (max (max m1 m2) m3) m4) m5) m6 := by{
            simp
            }
            have ha2 : a2 ∈ constructible_numbers_rec M (h0) (h1) m2 := by{
              aesop
            }
            exact constructible_numbers_rec_element_of M h0 h1 m2 (max (max (max (max (max m1 m2) m3) m4) m5) m6) hm2' a2 ha2
          · have hm4': m4 ≤ max (max (max (max (max m1 m2) m3) m4) m5) m6 := by{
            simp
            }
            have hb2 : b2 ∈ constructible_numbers_rec M (h0) (h1) m4 := by{
              aesop
            }
            exact constructible_numbers_rec_element_of M h0 h1 m4 (max (max (max (max (max m1 m2) m3) m4) m5) m6) hm4' b2 hb2
    }
    simp
    use c₁
    constructor
    · exact hc1'
    · use c₂
  }
  have hz' : z ∈ constructible_numbers_rec M (h0) (h1) (max (max (max (max (max m1 m2) m3) m4) m5) m6 + 1) := by{
    exact this hz
  }
  exact constructible_numbers_rec_subset_constructible_numbers M h0 h1 (max (max (max (max (max m1 m2) m3) m4) m5) m6 + 1) hz'
}

lemma element_line_circle_intersection_constructible (M : Set ℂ) (h0: 0 ∈ M) (h1: 1 ∈ M) (l : line_through_two_points) (c : circle_with_radius) (hl: l ∈ constructible_lines (constructible_numbers M h0 h1)) (hc: c ∈ constructible_circles (constructible_numbers M h0 h1)) (z : ℂ) (hz : z ∈ line_circle_intersection l c) : z ∈ constructible_numbers M (h0) (h1) := by{
  obtain⟨z₁, z₂, hl', hz₁, hz₂⟩ := hl
  obtain⟨p, a, b, hc', hp, ha, hb⟩ := hc
  obtain⟨ M1, hf1, hM1⟩ := ha
  obtain⟨ m1, hm1⟩ := hf1
  obtain⟨ M2, hf2, hM2⟩ := hb
  obtain⟨ m2, hm2⟩ := hf2
  obtain ⟨M3, hf3, hM3⟩ := hp
  obtain ⟨m3, hm3⟩ := hf3
  obtain ⟨M4, hf4, hM4⟩ := hz₁
  obtain ⟨m4, hm4⟩ := hf4
  obtain ⟨M5, hf5, hM5⟩ := hz₂
  obtain ⟨m5, hm5⟩ := hf5
  have : line_circle_intersection l c ⊆ constructible_numbers_rec M (h0) (h1) (max (max (max (max m1 m2) m3) m4) m5 + 1) := by{
    intros z hz
    unfold constructible_numbers_rec
    simp
    right
    unfold intersections
    left
    right
    have hl'' : l ∈ constructible_lines (constructible_numbers_rec M (h0) (h1) (max (max (max (max m1 m2) m3) m4) m5)) := by{
      use z₁
      use z₂
      constructor
      · exact hl'
      · constructor
        · have hm4': m4 ≤ max (max (max (max m1 m2) m3) m4) m5 := by{
            simp
          }
          have hz₁ : z₁ ∈ constructible_numbers_rec M (h0) (h1) m4 := by{
            aesop
          }
          exact constructible_numbers_rec_element_of M h0 h1 m4 (max (max (max (max m1 m2) m3) m4) m5) hm4' z₁ hz₁
        · have hm5': m5 ≤ max (max (max (max m1 m2) m3) m4) m5 := by{
            simp
          }
          have hz₂ : z₂ ∈ constructible_numbers_rec M (h0) (h1) m5 := by{
            aesop
          }
          exact constructible_numbers_rec_element_of M h0 h1 m5 (max (max (max (max m1 m2) m3) m4) m5) hm5' z₂ hz₂
    }

    have hc' : c ∈ constructible_circles (constructible_numbers_rec M (h0) (h1) (max (max (max (max m1 m2) m3) m4) m5)) := by{
      use p
      use a
      use b
      simp
      constructor
      · exact hc'
      · constructor
        · have hm3': m3 ≤ max (max (max (max m1 m2) m3) m4) m5 := by{
            simp
          }
          have hp : p ∈ constructible_numbers_rec M (h0) (h1) m3 := by{
            aesop
          }
          exact constructible_numbers_rec_element_of M h0 h1 m3 (max (max (max (max m1 m2) m3) m4) m5) hm3' p hp
        · constructor
          · have hm1': m1 ≤ max (max (max (max m1 m2) m3) m4) m5 := by{
            simp
            }
            have ha : a ∈ constructible_numbers_rec M (h0) (h1) m1 := by{
              aesop
            }
            exact constructible_numbers_rec_element_of M h0 h1 m1 (max (max (max (max m1 m2) m3) m4) m5) hm1' a ha
          · have hm2': m2 ≤ max (max (max (max m1 m2) m3) m4) m5 := by{
            simp
            }
            have hb : b ∈ constructible_numbers_rec M (h0) (h1) m2 := by{
              aesop
            }
            exact constructible_numbers_rec_element_of M h0 h1 m2 (max (max (max (max m1 m2) m3) m4) m5) hm2' b hb
    }
    simp
    use l
    constructor
    · exact hl''
    · use c
  }
  have hz' : z ∈ constructible_numbers_rec M (h0) (h1) (max (max (max (max m1 m2) m3) m4) m5 + 1) := by{
    exact this hz
  }
  exact constructible_numbers_rec_subset_constructible_numbers M h0 h1 (max (max (max (max m1 m2) m3) m4) m5 + 1) hz'
}

lemma element_line_line_intersection_constructible (M : Set ℂ) (h0 : 0 ∈ M) (h1: 1 ∈ M) (l₁ l₂ : line_through_two_points) (hl₁: l₁ ∈  constructible_lines (constructible_numbers M h0 h1)) (hl₂ : l₂ ∈  constructible_lines (constructible_numbers M h0 h1)) (z : ℂ) (hll : l₁.points ≠ l₂.points) (hz : z ∈ line_line_intersection l₁ l₂) : z ∈ constructible_numbers M (h0) (h1) := by{
  obtain⟨z₁, z₂, hl₁', hz₁, hz₂⟩ := hl₁
  obtain⟨z₃, z₄, hl₂', hz₃, hz₄⟩ := hl₂
  obtain⟨ M1, hf1, hM1⟩ := hz₁
  obtain⟨ m1, hm1⟩ := hf1
  obtain⟨ M2, hf2, hM2⟩ := hz₂
  obtain⟨ m2, hm2⟩ := hf2
  obtain⟨ M3, hf3, hM3⟩ := hz₃
  obtain⟨ m3, hm3⟩ := hf3
  obtain⟨ M4, hf4, hM4⟩ := hz₄
  obtain⟨ m4, hm4⟩ := hf4
  have : line_line_intersection l₁ l₂ ⊆ constructible_numbers_rec M (h0) (h1) (max (max (max m1 m2) m3) m4 + 1) := by{
    intros z hz
    unfold constructible_numbers_rec
    simp
    right
    unfold intersections
    left
    left
    have hl₁'' : l₁ ∈ constructible_lines (constructible_numbers_rec M (h0) (h1) (max (max (max m1 m2) m3) m4)) := by{
      use z₁
      use z₂
      constructor
      · exact hl₁'
      · constructor
        · have hm1': m1 ≤ max (max (max m1 m2) m3) m4 := by{
            simp
          }
          have hz₁ : z₁ ∈ constructible_numbers_rec M (h0) (h1) m1 := by{
            aesop
          }
          exact constructible_numbers_rec_element_of M h0 h1 m1 (max (max (max m1 m2) m3) m4) hm1' z₁ hz₁
        · have hm2': m2 ≤ max (max (max m1 m2) m3) m4 := by{
            simp
          }
          have hz₂ : z₂ ∈ constructible_numbers_rec M (h0) (h1) m2 := by{
            aesop
          }
          exact constructible_numbers_rec_element_of M h0 h1 m2 (max (max (max m1 m2) m3) m4) hm2' z₂ hz₂
    }

    have hl₂'' : l₂ ∈ constructible_lines (constructible_numbers_rec M (h0) (h1) (max (max (max m1 m2) m3) m4)) := by{
      use z₃
      use z₄
      constructor
      · exact hl₂'
      · constructor
        · have hm3': m3 ≤ max (max (max m1 m2) m3) m4 := by{
            simp
          }
          have hz₃ : z₃ ∈ constructible_numbers_rec M (h0) (h1) m3 := by{
            aesop
          }
          exact constructible_numbers_rec_element_of M h0 h1 m3 (max (max (max m1 m2) m3) m4) hm3' z₃ hz₃
        · have hm4': m4 ≤ max (max (max m1 m2) m3) m4 := by{
            simp
          }
          have hz₄ : z₄ ∈ constructible_numbers_rec M (h0) (h1) m4 := by{
            aesop
          }
          exact constructible_numbers_rec_element_of M h0 h1 m4 (max (max (max m1 m2) m3) m4) hm4' z₄ hz₄
    }
    simp
    use l₁
    constructor
    · exact hl₁''
    · use l₂
  }
  have hz' : z ∈ constructible_numbers_rec M (h0) (h1) (max (max (max m1 m2) m3) m4 + 1) := by{
    exact this hz
  }
  exact constructible_numbers_rec_subset_constructible_numbers M h0 h1 (max (max (max m1 m2) m3) m4 + 1) hz'
}

lemma constructible_numbers_element_of (M : Set ℂ) (h0: 0 ∈ M) (h1: 1 ∈ M) (a : ℂ) (ha: a ∈ M) : a ∈ constructible_numbers M (h0) (h1) := by{
  have h1 : constructible_numbers_rec M (h0) (h1) 0 ⊆ constructible_numbers M (h0) (h1) := by{
     apply Set.subset_sUnion_of_mem
     use 0
  }
  exact h1 ha
}

theorem constructible_numbers_closed_addition (M: Set ℂ) (h0 : 0 ∈ M) (h1: 1 ∈ M)
(a b : ℂ) (ha: a ∈ constructible_numbers M (h0) (h1)) (hb: b ∈ constructible_numbers M (h0) (h1)): (a + b : ℂ) ∈ constructible_numbers M (h0) (h1) := by{
 by_cases h : a ≠ b
 ·let c1 : circle_with_radius := {center := b, radius := Complex.abs (a)}
  let c2 : circle_with_radius := {center := a, radius := Complex.abs (b)}

  have h2 : c1 ∈ constructible_circles (constructible_numbers M (h0) (h1)) := by{
     use b
     use a
     use 0
     simp
     constructor
     · exact hb
     · constructor
       · exact ha
       · exact constructible_numbers_element_of M h0 h1 0 h0
  }
  have h3 : c2 ∈ constructible_circles (constructible_numbers M (h0) (h1)) := by{
     use a
     use b
     use 0
     simp
     constructor
     · exact ha
     · constructor
       · exact hb
       · exact constructible_numbers_element_of M h0 h1 0 h0
  }

  have hcc : c1 ≠ c2 := by{
    simp
    intro hcc'
    have hcc'': Complex.abs a = Complex.abs b := by{
      simp [hcc']
    }
    exact (h (id hcc'.symm)).elim
   }

  have h1' : (a + b : ℂ) ∈ c1.points ∩ c2.points := by{
     constructor
     · simp
       calc Complex.abs (a + b - b) = Complex.abs a := by simp
       _= c1.radius := by exact rfl
     · simp
       calc Complex.abs (a + b - a) = Complex.abs b := by simp
       _= c2.radius := by exact rfl
  }
  exact element_circle_circle_intersection_constructible M h0 h1 c1 c2 h2 h3 (hcc) (a + b) h1'
 · push_neg at h
   let l : line_through_two_points := {z₁ := 0, z₂ := a}
   let c : circle_with_radius := {center := a, radius := Complex.abs (a)}
   have h2 : l ∈ constructible_lines (constructible_numbers M (h0) (h1)) := by{
     use 0
     use a
     simp
     constructor
     · exact constructible_numbers_element_of M h0 h1 0 h0
     · exact ha
   }
   have h3 : c ∈ constructible_circles (constructible_numbers M (h0) (h1)) := by{
     use a
     use a
     use 0
     simp
     constructor
     · exact ha
     · exact constructible_numbers_element_of M h0 h1 0 h0
   }
   rw [←h]
   have h4: a + a ∈ l.points ∩ c.points := by{
     constructor
     · use -1
       simp
       ring
     · simp
       calc Complex.abs (a + a - a) = Complex.abs a := by simp
       _= c.radius := by exact rfl
   }
   exact element_line_circle_intersection_constructible M h0 h1 l c h2 h3 (a + a) h4
}

theorem constructible_numbers_additive_inverse (M : Set ℂ) (h0: 0 ∈  M) (h1 : 1 ∈ M) (a : ℂ) (ha: a ∈ constructible_numbers M (h0) (h1)) :
  -a ∈ constructible_numbers M (h0) (h1) := by{
  let L : line_through_two_points := {z₁ := 0, z₂ := a}
  let C : circle_with_radius := {center := 0, radius := Complex.abs a}

  have hL : L ∈ constructible_lines (constructible_numbers M (h0) (h1)) := by{
    use 0
    use a
    simp
    constructor
    · exact constructible_numbers_element_of M h0 h1 0 h0
    · exact ha
  }
  have hC : C ∈ constructible_circles (constructible_numbers M (h0) (h1)) := by{
    use 0
    use a
    use 0
    simp
    constructor
    · exact constructible_numbers_element_of M h0 h1 0 h0
    · constructor
      · exact ha
      · exact constructible_numbers_element_of M h0 h1 0 h0
  }

  have h : -a ∈ line_circle_intersection L C := by{
  constructor
  · use 2
    simp
    ring
  · calc Complex.abs (-a - 0) = Complex.abs a := by simp
    _= C.radius := by exact rfl
  }

  exact element_line_circle_intersection_constructible M h0 h1 L C hL hC (-a) h
}

open ComplexConjugate

lemma constructible_numbers_closed_complex_conjugation (M : Set ℂ) (h0: 0∈M) (h1: 1∈M) (z : ℂ) (hz: z ∈ constructible_numbers M (h0) (h1)):
  conj z ∈ constructible_numbers M (h0) (h1) := by{
    have this : conj z = ⟨z.re, -z.im⟩ := by exact rfl
    rw[this]
    let C1 : circle_with_radius := {center := 0, radius := Complex.abs z}
    let C2 : circle_with_radius := {center := 1, radius := Complex.abs (z-1)}
    have hC1 : C1 ∈ constructible_circles (constructible_numbers M (h0) (h1)) := by{
      use 0
      use z
      use 0
      simp
      constructor
      · exact constructible_numbers_element_of M h0 h1 0 h0
      · constructor
        · exact hz
        · exact constructible_numbers_element_of M h0 h1 0 h0

    }
    have hC2 : C2 ∈ constructible_circles (constructible_numbers M (h0) (h1)) := by{
      use 1
      use z
      use 1
      simp
      constructor
      · exact constructible_numbers_element_of M h0 h1 1 h1
      · constructor
        · exact hz
        · exact constructible_numbers_element_of M h0 h1 1 h1
    }
    have hcc : C1 ≠ C2 := by{
      simp
    }
    have hz1: z ∈ C1.points ∩ C2.points := by{
      constructor
      · calc Complex.abs (z - 0) = Complex.abs z := by simp
        _= C1.radius := by exact rfl
      · calc Complex.abs (z - 1) = C2.radius := by simp
    }
    have hz2 : ⟨z.re, -z.im⟩  ∈ circle_circle_intersection C1 C2 := by{
      constructor
      · calc Complex.abs (⟨z.re, -z.im⟩ - 0) = Complex.abs ⟨z.re, -z.im⟩ := by simp
        _= Real.sqrt (Complex.normSq ⟨z.re, -z.im⟩) := by exact rfl
        _= Real.sqrt (z.re*z.re + z.im*z.im) := by simp
        _= C1.radius := by exact rfl
      · calc Complex.abs (⟨z.re, -z.im⟩ - 1) = Complex.abs (⟨z.re, -z.im⟩ - ⟨1, 0⟩) := by exact rfl
        _= Complex.abs (⟨z.re -1, -z.im - 0⟩ ) := by exact rfl
        _= Complex.abs ⟨z.re -1, -z.im ⟩ := by simp
        _= Real.sqrt ((z.re -1)*(z.re -1) + (-z.im)*(-z.im)) := by exact rfl
        _= Real.sqrt ((z.re -1)*(z.re -1) + (z.im)*(z.im)) := by simp
        _= Real.sqrt (Complex.normSq ⟨z.re -1, z.im⟩) := by simp
        _= Complex.abs ⟨z.re -1, z.im⟩ := by exact rfl
        _= Complex.abs ⟨z.re -1, z.im-0⟩ := by ring
        _= Complex.abs (⟨z.re , z.im⟩ - ⟨ 1, 0⟩ ) := by exact rfl
        _= Complex.abs (z - 1) := by exact rfl
        _= C2.radius := by exact rfl
    }
    exact element_circle_circle_intersection_constructible M h0 h1 C1 C2 hC1 hC2 hcc ⟨ z.re,-z.im ⟩ hz2
}

lemma constructible_numbers_contains_I (M : Set ℂ) (h0: 0 ∈ M) (h1: 1 ∈ M) : (Complex.I : ℂ) ∈ constructible_numbers M (h0) (h1) := by{
  have ha : -1 ∈ constructible_numbers M h0 h1 := by{
    exact constructible_numbers_additive_inverse M h0 h1 1 (constructible_numbers_element_of M h0 h1 1 h1)
  }
  let C1 : circle_with_radius := {center := 1, radius := 2}
  let C2 : circle_with_radius := {center := -1, radius := 2}
  have hC1 : C1 ∈ constructible_circles (constructible_numbers M (h0) (h1)) := by{
    use 1
    use 1
    use -1
    simp
    constructor
    · calc 2 = Complex.abs 2 := by exact Complex.abs_two.symm
      _= Complex.abs (1 + 1):= by ring
    · constructor
      · exact constructible_numbers_element_of M h0 h1 1 h1
      · exact ha
  }
  have hC2 : C2 ∈ constructible_circles (constructible_numbers M (h0) (h1)) := by{
    use -1
    use 1
    use -1
    simp
    constructor
    · calc 2 = Complex.abs 2 := by exact Complex.abs_two.symm
      _= Complex.abs (1 + 1):= by ring
    · constructor
      · exact ha
      · constructor
        · exact constructible_numbers_element_of M h0 h1 1 h1
        · exact ha
  }
  have hcc : C1 ≠ C2 := by {
    simp
  }
  let z₁ : ℂ := ⟨0, Real.sqrt 3⟩
  have hz₁ : z₁ ∈ C1.points ∩ C2.points := by{
    constructor
    · calc Complex.abs (z₁ - 1) = Complex.abs (⟨0, Real.sqrt 3⟩ - ⟨ 1, 0⟩) := by exact rfl
      _= Complex.abs ⟨0-1, Real.sqrt 3 -0⟩ := by exact rfl
      _= Complex.abs ⟨-1, Real.sqrt 3⟩ := by ring
      _= Real.sqrt ((-1)*(-1) + Real.sqrt 3 * Real.sqrt 3) := by exact rfl
      _= Real.sqrt (1 + 3) := by norm_num
      _= Real.sqrt (2*2) := by ring
      _= 2 := by exact Real.sqrt_mul_self (by norm_num)
      _= C1.radius := by exact rfl

    · calc Complex.abs (z₁ - (-1)) = Complex.abs (z₁ + 1) := by norm_num
      _= Complex.abs (⟨0, Real.sqrt 3⟩ + ⟨ 1, 0⟩) := by exact rfl
      _= Complex.abs ⟨0+1, Real.sqrt 3 + 0⟩ := by exact rfl
      _= Complex.abs ⟨1, Real.sqrt 3⟩ := by ring
      _= Real.sqrt (1*1 + Real.sqrt 3 * Real.sqrt 3) := by exact rfl
      _= Real.sqrt (1 + 3) := by norm_num
      _= Real.sqrt 4 := by ring
      _= Real.sqrt (2*2) := by norm_num
      _= 2 := by exact Real.sqrt_mul_self (by norm_num)
      _= C2.radius := by exact rfl
  }

  have hz₁' : z₁ ∈ constructible_numbers M (h0) (h1)  := by{
    exact element_circle_circle_intersection_constructible M h0 h1 C1 C2 hC1 hC2 hcc z₁ hz₁
  }

  let L1 : line_through_two_points := {z₁ := z₁, z₂ := 0}
  let C3 : circle_with_radius := {center := 0, radius := 1}
  have hL : L1 ∈ constructible_lines (constructible_numbers M (h0) (h1)) := by{
    use z₁
    use 0
    simp
    constructor
    · exact hz₁'
    · exact constructible_numbers_element_of M h0 h1 0 h0
  }
  have hC3 : C3 ∈ constructible_circles (constructible_numbers M (h0) (h1)) := by{
    use 0
    use 1
    use 0
    simp
    constructor
    · exact constructible_numbers_element_of M h0 h1 0 h0
    · constructor
      · exact constructible_numbers_element_of M h0 h1 1 h1
      · exact constructible_numbers_element_of M h0 h1 0 h0
  }

  have hI₁ : Complex.I ∈ L1.points ∩ C3.points := by{
    constructor
    · use (1 / Real.sqrt 3)
      calc (1 / Real.sqrt 3 : ℝ ) * L1.z₁ + (1 - (1 / Real.sqrt 3 : ℝ ) ) * L1.z₂ = (1 / Real.sqrt 3 : ℝ ) * z₁ + (1 - (1 / Real.sqrt 3 : ℝ ) ) * 0 := by exact rfl
      _= (1 / Real.sqrt 3) * z₁ + (1 / Real.sqrt 3) * 0 := by norm_num
      _= (1 / Real.sqrt 3) * z₁ := by ring
      _= (1 / Real.sqrt 3) * ⟨0, Real.sqrt 3⟩ := by exact rfl
      _= ⟨(1 / Real.sqrt 3) * 0, (1 / Real.sqrt 3) * Real.sqrt 3⟩ := by {
        refine Complex.ext_iff.mpr ?_
        constructor
        · simp
        · simp
      }
      _= ⟨0, 1⟩ := by norm_num
      _= Complex.I := by exact rfl
    · calc Complex.abs (Complex.I - 0) = Complex.abs (⟨0, 1⟩ - ⟨0,0⟩) := by exact rfl
      _= Complex.abs ⟨0-0, 1-0⟩ := by exact rfl
      _= Complex.abs ⟨0, 1⟩ := by ring
      _= Real.sqrt (0*0 + 1*1) := by exact rfl
      _= 1 := by norm_num
      _= C3.radius := by exact rfl
  }
  exact element_line_circle_intersection_constructible M h0 h1 L1 C3 hL hC3 Complex.I hI₁
}

lemma constructible_numbers_half_point (M: Set ℂ) (h0 : 0 ∈ M) (h1: 1 ∈ M) (z₁ z₂ : ℂ) (hz₁ : z₁ ∈ constructible_numbers M (h0) (h1)) (hz₂ : z₂ ∈ constructible_numbers M (h0) (h1))  : (z₁ + z₂) / 2 ∈ constructible_numbers M (h0) (h1) := by{
  by_cases h' : z₁ = z₂
  have : (z₁ + z₂) / 2 = z₁ := by{
    rw [h']
    simp
  }
  rw[this]
  exact hz₁

  push_neg at h'
  let c1 : circle_with_radius := {center := z₁, radius := Complex.abs (z₂ - z₁)}
  have hc₁: c1 ∈ constructible_circles (constructible_numbers M (h0) (h1)) := by{
    use z₁
    use z₂
    use z₁
  }
  let c2 : circle_with_radius := {center := z₂, radius := Complex.abs (z₂ - z₁)}
  have hc₂: c2 ∈ constructible_circles (constructible_numbers M (h0) (h1)) := by{
    use z₂
    use z₂
    use z₁
  }
  have hcc : c1 ≠ c2 := by{
    simp
    push_neg
    exact h'
  }
  have hh: Real.sqrt ((1/(2*2)) + (Real.sqrt (3) * Real.sqrt (3) / (2 * 2))) = 1 := by{  --useful for many simplifications later
   calc Real.sqrt ((1/(2*2)) + (Real.sqrt (3) * Real.sqrt (3) / (2 * 2))) =Real.sqrt (1/4 + 3/4):= by norm_num
   _= Real.sqrt (1) := by norm_num
   _= 1 := by simp
  }

  by_cases h: z₁.im = z₂.im
  · let x : ℝ := (z₁.re + z₂.re) / 2
    let y₁ : ℝ := 1 / 2 * Real.sqrt (3) * (z₁.re - z₂.re) + z₁.im
    let y₂ : ℝ := - 1 / 2 * Real.sqrt (3) * (z₁.re - z₂.re) + z₁.im
    let s₁ : ℂ := ⟨x, y₁⟩
    let s₂ : ℂ := ⟨x, y₂⟩
    have hs₁ : s₁ ∈ c1.points ∩ c2.points := by{
      constructor
      · calc Complex.abs (s₁ - z₁) = Complex.abs (⟨x,y₁⟩ - ⟨z₁.re, z₁.im⟩) := by exact rfl
        _= Complex.abs ⟨x - z₁.re, y₁ - z₁.im⟩ := by exact rfl
        _= Complex.abs ⟨(z₁.re + z₂.re) / 2 - z₁.re, 1 / 2 * Real.sqrt (3) * (z₁.re - z₂.re) + z₁.im - z₁.im⟩ := by exact rfl
        _= Complex.abs ⟨( z₂.re - z₁.re) / 2, - 1 / 2 * Real.sqrt (3) * (z₂.re - z₁.re)⟩ := by ring
        _= Real.sqrt (((z₂.re - z₁.re) / 2)*((z₂.re - z₁.re) / 2) + (- 1 / 2 * Real.sqrt (3) * (z₂.re - z₁.re))*(- 1 / 2 * Real.sqrt (3) * (z₂.re - z₁.re))) := by exact rfl
        _= Real.sqrt ((z₂.re - z₁.re) * (z₂.re -z₁.re) * (1 / (2*2) + ( 1 / 2 * Real.sqrt (3)) * ( 1 / 2 * Real.sqrt (3)))) := by ring
        _= Real.sqrt ((z₂.re - z₁.re) * (z₂.re -z₁.re)) * Real.sqrt (1 / (2*2) + (1 / 2 * Real.sqrt (3)) * ( 1 / 2 * Real.sqrt (3))) := by {
          exact Real.sqrt_mul (mul_self_nonneg (z₂.re - z₁.re)) (1 / (2*2) + (1 / 2 * Real.sqrt (3)) * ( 1 / 2 * Real.sqrt (3)))
        }
        _= Real.sqrt ((z₂.re - z₁.re) * (z₂.re -z₁.re)) * Real.sqrt (1 / (2*2) + (Real.sqrt (3) * Real.sqrt (3)) / (2*2) ) := by ring
        _= Real.sqrt ((z₂.re - z₁.re) * (z₂.re -z₁.re)) * 1 := by rw[hh]
        _= Real.sqrt ((z₂.re - z₁.re) * (z₂.re -z₁.re) + 0) := by ring
        _= Real.sqrt ((z₂.re - z₁.re) * (z₂.re -z₁.re) + (z₂.im - z₁.im) * (z₂.im - z₁.im)) := by {
          have : z₂.im - z₁.im = 0 := by {
            rw[h]
            simp
          }
          rw[this]
          ring
        }
        _= Complex.abs ⟨z₂.re - z₁.re, z₂.im - z₁.im⟩ := by exact rfl
        _= Complex.abs (⟨z₂.re, z₂.im⟩ - ⟨z₁.re, z₁.im⟩)  := by exact rfl
        _= Complex.abs (z₂ - z₁) := by exact rfl
        _= c1.radius := by exact rfl
      · calc Complex.abs (s₁ - z₂) = Complex.abs (⟨x,y₁⟩ - ⟨z₂.re, z₂.im⟩) := by exact rfl
        _= Complex.abs ⟨x - z₂.re, y₁ - z₂.im⟩ := by exact rfl
        _= Complex.abs ⟨(z₁.re + z₂.re) / 2 - z₂.re, 1 / 2 * Real.sqrt (3) * (z₁.re - z₂.re) + z₁.im - z₂.im⟩ := by exact rfl
        _= Complex.abs ⟨(z₁.re + z₂.re) / 2 - z₂.re, 1 / 2 * Real.sqrt (3) * (z₁.re - z₂.re) + z₁.im - z₁.im⟩ := by rw[h]
        _= Complex.abs ⟨( z₁.re - z₂.re) / 2, 1 / 2 * Real.sqrt (3) * (z₁.re - z₂.re)⟩ := by ring
        _= Real.sqrt (((z₁.re - z₂.re) / 2)*((z₁.re - z₂.re) / 2) + (1 / 2 * Real.sqrt (3) * (z₁.re - z₂.re))*(1 / 2 * Real.sqrt (3) * (z₁.re - z₂.re))) := by exact rfl
        _= Real.sqrt ((z₁.re - z₂.re) * (z₁.re -z₂.re) * (1 / (2*2) + (1 / 2 * Real.sqrt (3)) * (1 / 2 * Real.sqrt (3)))) := by ring
        _= Real.sqrt ((z₁.re - z₂.re) * (z₁.re -z₂.re)) * Real.sqrt (1 / (2*2) + ( 1 / 2 * Real.sqrt (3)) * ( 1 / 2 * Real.sqrt (3))) := by {
          exact Real.sqrt_mul (mul_self_nonneg (z₁.re - z₂.re)) (1 / (2*2) + ( 1 / 2 * Real.sqrt (3)) * ( 1 / 2 * Real.sqrt (3)))
        }
        _= Real.sqrt ((z₁.re - z₂.re) * (z₁.re -z₂.re)) * Real.sqrt (1 / (2*2) + (Real.sqrt (3) * Real.sqrt (3)) / (2 *2 )) := by ring
        _= Real.sqrt ((z₁.re - z₂.re) * (z₁.re -z₂.re)) * 1 := by rw[hh]
        _= Real.sqrt ((z₁.re - z₂.re) * (z₁.re -z₂.re)) := by simp
        _= Real.sqrt ((z₁.re - z₂.re) * (z₁.re -z₂.re) + 0) := by ring
        _= Real.sqrt ((z₁.re - z₂.re) * (z₁.re -z₂.re) + (z₁.im - z₂.im) * (z₁.im - z₂.im)) := by {
          have : z₁.im - z₂.im = 0 := by {
            rw[h]
            simp
          }
          rw[this]
          ring
        }
        _= Complex.abs ⟨z₁.re - z₂.re, z₁.im - z₂.im⟩ := by exact rfl
        _= Complex.abs (⟨z₁.re, z₁.im⟩ - ⟨z₂.re, z₂.im⟩)  := by exact rfl
        _= Complex.abs (z₁ - z₂) := by exact rfl
        _= Complex.abs (z₂ - z₁) := by rw [@AbsoluteValue.map_sub]
        _= c2.radius := by exact rfl
    }
    have hs₁' : s₁ ∈ constructible_numbers M (h0) (h1) := by{
      exact element_circle_circle_intersection_constructible M h0 h1 c1 c2 hc₁ hc₂ hcc s₁ hs₁
    }
    have hs₂ : s₂ ∈ c1.points ∩ c2.points := by{

      constructor
      · calc Complex.abs (s₂ - z₁) = Complex.abs (⟨x,y₂⟩ - ⟨z₁.re, z₁.im⟩) := by exact rfl
        _= Complex.abs ⟨x - z₁.re, y₂ - z₁.im⟩ := by exact rfl
        _= Complex.abs ⟨(z₁.re + z₂.re) / 2 - z₁.re, - 1 / 2 * Real.sqrt (3) * (z₁.re - z₂.re) + z₁.im - z₁.im⟩ := by exact rfl
        _= Complex.abs ⟨( z₂.re - z₁.re) / 2, 1 / 2 * Real.sqrt (3) * (z₂.re - z₁.re)⟩ := by ring
        _= Real.sqrt (((z₂.re - z₁.re) / 2)*((z₂.re - z₁.re) / 2) + (1 / 2 * Real.sqrt (3) * (z₂.re - z₁.re))*(1 / 2 * Real.sqrt (3) * (z₂.re - z₁.re))) := by exact rfl
        _= Real.sqrt ((z₂.re - z₁.re) * (z₂.re -z₁.re) * (1 / (2*2) + (- 1 / 2 * Real.sqrt (3)) * (- 1 / 2 * Real.sqrt (3)))) := by ring
        _= Real.sqrt ((z₂.re - z₁.re) * (z₂.re -z₁.re)) * Real.sqrt (1 / (2*2) + (- 1 / 2 * Real.sqrt (3)) * (- 1 / 2 * Real.sqrt (3))) := by {
          exact Real.sqrt_mul (mul_self_nonneg (z₂.re - z₁.re)) (1 / (2*2) + (- 1 / 2 * Real.sqrt (3)) * (- 1 / 2 * Real.sqrt (3)))
        }
        _= Real.sqrt ((z₂.re - z₁.re) * (z₂.re -z₁.re)) * Real.sqrt (1 / (2*2) + (Real.sqrt (3) * Real.sqrt (3)) / (2 *2)) := by ring
        _= Real.sqrt ((z₂.re - z₁.re) * (z₂.re -z₁.re)) * 1 := by rw[hh]
        _= Real.sqrt ((z₂.re - z₁.re) * (z₂.re -z₁.re)) := by simp
        _= Real.sqrt ((z₂.re - z₁.re) * (z₂.re -z₁.re) + 0) := by ring
        _= Real.sqrt ((z₂.re - z₁.re) * (z₂.re -z₁.re) + (z₂.im - z₁.im) * (z₂.im - z₁.im)) := by {
          have : z₂.im - z₁.im = 0 := by {
            rw[h]
            simp
          }
          rw[this]
          ring
        }
        _= Complex.abs ⟨z₂.re - z₁.re, z₂.im - z₁.im⟩ := by exact rfl
        _= Complex.abs (⟨z₂.re, z₂.im⟩ - ⟨z₁.re, z₁.im⟩)  := by exact rfl
        _= Complex.abs (z₂ - z₁) := by exact rfl
        _= c1.radius := by exact rfl
      · calc Complex.abs (s₂ - z₂) = Complex.abs (⟨x,y₂⟩ - ⟨z₂.re, z₂.im⟩) := by exact rfl
        _= Complex.abs ⟨x - z₂.re, y₂ - z₂.im⟩ := by exact rfl
        _= Complex.abs ⟨(z₁.re + z₂.re) / 2 - z₂.re, - 1 / 2 * Real.sqrt (3) * (z₁.re - z₂.re) + z₁.im - z₂.im⟩ := by exact rfl
        _= Complex.abs ⟨(z₁.re + z₂.re) / 2 - z₂.re, - 1 / 2 * Real.sqrt (3) * (z₁.re - z₂.re) + z₁.im - z₁.im⟩ := by rw[h]
        _= Complex.abs ⟨( z₁.re - z₂.re) / 2, - 1 / 2 * Real.sqrt (3) * (z₁.re - z₂.re)⟩ := by ring
        _= Real.sqrt (((z₁.re - z₂.re) / 2)*((z₁.re - z₂.re) / 2) + (- 1 / 2 * Real.sqrt (3) * (z₁.re - z₂.re))*(- 1 / 2 * Real.sqrt (3) * (z₁.re - z₂.re))) := by exact rfl
        _= Real.sqrt ((z₁.re - z₂.re) * (z₁.re -z₂.re) * (1 / (2*2) + ( 1 / 2 * Real.sqrt (3)) * ( 1 / 2 * Real.sqrt (3)))) := by ring
        _= Real.sqrt ((z₁.re - z₂.re) * (z₁.re -z₂.re)) * Real.sqrt (1 / (2*2) + (1 / 2 * Real.sqrt (3)) * ( 1 / 2 * Real.sqrt (3)) ) := by {
          exact Real.sqrt_mul (mul_self_nonneg (z₁.re - z₂.re)) (1 / (2*2) + (1 / 2 * Real.sqrt (3)) * ( 1 / 2 * Real.sqrt (3)))
        }
        _= Real.sqrt ((z₁.re - z₂.re) * (z₁.re -z₂.re)) * Real.sqrt (1 / (2*2) + (Real.sqrt (3) * Real.sqrt (3)) / (2*2)) := by ring
        _= Real.sqrt ((z₁.re - z₂.re) * (z₁.re -z₂.re)) * 1 := by rw[hh]
        _= Real.sqrt ((z₁.re - z₂.re) * (z₁.re -z₂.re)) := by simp
        _= Real.sqrt ((z₁.re - z₂.re) * (z₁.re -z₂.re) + 0) := by ring
        _= Real.sqrt ((z₁.re - z₂.re) * (z₁.re -z₂.re) + (z₁.im - z₂.im) * (z₁.im - z₂.im)) := by {
          have : z₁.im - z₂.im = 0 := by {
            rw[h]
            simp
          }
          rw[this]
          ring
        }
        _= Complex.abs ⟨z₁.re - z₂.re, z₁.im - z₂.im⟩ := by exact rfl
        _= Complex.abs (⟨z₁.re, z₁.im⟩ - ⟨z₂.re, z₂.im⟩)  := by exact rfl
        _= Complex.abs (z₁ - z₂) := by exact rfl
        _= Complex.abs (z₂ - z₁) := by rw [@AbsoluteValue.map_sub]
        _= c2.radius := by exact rfl

    }
    have hs₂' : s₂ ∈ constructible_numbers M (h0) (h1) := by{
      exact element_circle_circle_intersection_constructible M h0 h1 c1 c2 hc₁ hc₂ hcc s₂ hs₂
    }
    let L1 : line_through_two_points := {z₁ := s₁, z₂ := s₂}
    have hL1 : L1 ∈ constructible_lines (constructible_numbers M (h0) (h1)) := by{
      use s₁
      use s₂
    }
    let L2 : line_through_two_points := {z₁ := z₁, z₂ := z₂}
    have hL2 : L2 ∈ constructible_lines (constructible_numbers M (h0) (h1)) := by{
      use z₁
      use z₂
    }
    have hll : L1.points ≠ L2.points := by{
      have hll₁: z₁ ∈ L2.points := by exact line_through_two_points_beginn_in_points L2
      have hll₂: z₁ ∉ L1.points := by{
        unfold line_through_two_points.points
        simp
        intro t
        ring
        intro hsmth
        simp at hsmth
        apply_fun Complex.re at hsmth
        simp at hsmth
        have : z₁.re = z₂.re := by {
          apply_fun (fun x ↦ 2*x - z₁.re) at hsmth
          ring at hsmth
          exact id hsmth.symm
        }
        have : z₁ = z₂ := by {
          refine Complex.ext_iff.mpr ?_
          constructor
          · exact this
          · exact h
        }
        exact h' this
      }
      intro hsmth2
      rw[hsmth2] at hll₂
      exact hll₂ hll₁
    }
    have hz : (z₁ + z₂) / 2 ∈ L1.points ∩ L2.points := by{

      constructor
      · use 1/2
        calc (1 / 2 : ℝ ) * L1.z₁ + (1 - (1 / 2 : ℝ ) ) * L1.z₂ = (1 / 2 : ℝ ) * s₁ + (1 - (1 / 2 : ℝ ) ) * s₂ := by exact rfl
        _= (1 / 2 : ℝ ) * s₁ + (1 / 2 : ℝ ) * s₂ := by norm_num
        _= (1 / 2 : ℝ ) * ⟨x, y₁⟩ + (1 / 2 : ℝ ) * ⟨x, y₂⟩ := by exact rfl
        _= ⟨(1 / 2 : ℝ ) * x, (1 / 2 : ℝ ) * y₁⟩ + (1 / 2 : ℝ ) * ⟨x, y₂⟩ := by rw [Complex.ofReal_mul']
        _= ⟨(1 / 2 : ℝ ) * x, (1 / 2 : ℝ ) * y₁⟩ + ⟨(1 / 2 : ℝ ) * x, (1 / 2 : ℝ ) * y₂⟩ := by rw [Complex.ofReal_mul']
        _= ⟨(1 / 2 : ℝ ) * x + (1 / 2 : ℝ ) * x, (1 / 2 : ℝ ) * y₁ + (1 / 2 : ℝ ) * y₂⟩ := by exact rfl
        _= ⟨x, (1 / 2 ) * (y₁ + y₂)⟩ := by ring
        _= ⟨(z₁.re + z₂.re) / 2, (1 / 2 ) * ( (1 / 2 * Real.sqrt (3) * (z₁.re - z₂.re) + z₁.im) + (- 1 / 2 * Real.sqrt (3) * (z₁.re - z₂.re) + z₁.im))⟩ := by exact rfl
        _=  ⟨1/2 * (z₁.re + z₂.re), 1/2 *(z₁.im + z₁.im)⟩:= by ring
        _=  ⟨1/2 * (z₁.re + z₂.re), 1/2 *(z₁.im + z₂.im)⟩:= by rw[h]
        _=  ⟨(1/2 : ℝ)  * (z₁.re + z₂.re), (1/2 : ℝ ) *(z₁.im + z₂.im)⟩:= by simp
        _= ⟨ (1/2 : ℝ) * z₁.re + (1/2 : ℝ) * z₂.re, (1/2 : ℝ) * z₁.im + (1/2 : ℝ) * z₂.im⟩ := by ring
        _= ⟨ (1/2 : ℝ) * z₁.re , (1/2 : ℝ) * z₁.im⟩ + ⟨ (1/2 : ℝ) * z₂.re, (1/2 : ℝ) * z₂.im⟩ := by exact rfl
        _= (1/2 : ℂ  ) * z₁ + (1/2 : ℂ ) * z₂ := by {
          rw[← Complex.ofReal_mul']
          push_cast
          simp
          rw[← Complex.ofReal_mul']
          push_cast
          simp
          }
        _= (z₁ + z₂) / 2 := by ring
      · use 1/2
        calc (1/2 : ℝ ) * L2.z₁ + (1 - (1/2 : ℝ ) ) * L2.z₂ = (1/2) * z₁ + (1 - (1/2)) * z₂ := by simp
        _= (1/2) * z₁ + (1/2) * z₂ := by norm_num
        _= (z₁ + z₂) / 2 := by ring


    }
    exact element_line_line_intersection_constructible M h0 h1 L1 L2 hL1 hL2 ((z₁ + z₂) / 2) hll hz
  · let x₁ : ℝ := (1/2) * (z₁.re + z₂.re - Real.sqrt (3) * (z₁.im -z₂.im))
    let x₂ : ℝ := (1/2) * (z₁.re + z₂.re + Real.sqrt (3) * (z₁.im -z₂.im))
    let y₁ : ℝ := (1/ 2) * ((z₁.re - z₂.re) * Real.sqrt (3) + (z₁.im + z₂.im))
    let y₂ : ℝ := (1/ 2) * ((z₂.re - z₁.re) * Real.sqrt (3) + (z₁.im + z₂.im))
    let s₁ : ℂ := ⟨x₁, y₁⟩
    let s₂ : ℂ := ⟨x₂, y₂⟩
    have hs₁ : s₁ ∈ c1.points ∩ c2.points := by{
      let a : ℝ :=  (z₂.re - z₁.re)
      let b : ℝ :=  Real.sqrt (3) * (z₂.im - z₁.im)
      let c : ℝ := (- (z₂.re - z₁.re) * Real.sqrt (3))
      let d : ℝ := (z₂.im -  z₁.im)
      constructor
      · calc Complex.abs (s₁ - z₁) = Complex.abs (⟨x₁,y₁⟩ - ⟨z₁.re, z₁.im⟩) := by exact rfl
        _= Complex.abs ⟨x₁ - z₁.re, y₁ - z₁.im⟩ := by exact rfl
        _= Complex.abs ⟨(1/2) * (z₁.re + z₂.re - Real.sqrt (3) * (z₁.im -z₂.im)) - z₁.re, (1/ 2) * ((z₁.re - z₂.re) * Real.sqrt (3) + (z₁.im + z₂.im)) - z₁.im⟩ := by exact rfl
        _= Complex.abs ⟨(1/2) * (z₂.re - z₁.re) + (1/2) * Real.sqrt (3) * (z₂.im - z₁.im), -(1/2) * (z₂.re - z₁.re) * Real.sqrt (3) + (1/2) * (z₂.im -  z₁.im)⟩ := by ring
        _= Real.sqrt (((1/2) * (z₂.re - z₁.re) + (1/2) * Real.sqrt (3) * (z₂.im - z₁.im))*((1/2) * (z₂.re - z₁.re) + (1/2) * Real.sqrt (3) * (z₂.im - z₁.im)) + (-(1/2) * (z₂.re - z₁.re) * Real.sqrt (3) + (1/2) * (z₂.im -  z₁.im))*(-(1/2) * (z₂.re - z₁.re) * Real.sqrt (3) + (1/2) * (z₂.im -  z₁.im))) := by exact rfl
        _= Real.sqrt (((1/2) * (1/2) * (((z₂.re - z₁.re) + Real.sqrt (3) * (z₂.im - z₁.im))*((z₂.re - z₁.re) +  Real.sqrt (3) * (z₂.im - z₁.im)) + (- (z₂.re - z₁.re) * Real.sqrt (3) +  (z₂.im -  z₁.im))*(-(z₂.re - z₁.re) * Real.sqrt (3) + (z₂.im - z₁.im))))) := by ring
        _= Real.sqrt ((1/2) * (1/2)) * Real.sqrt (((z₂.re - z₁.re) + (Real.sqrt (3) * (z₂.im - z₁.im)))*((z₂.re - z₁.re) +  (Real.sqrt (3) * (z₂.im - z₁.im))) + ((- (z₂.re - z₁.re) * Real.sqrt (3)) +  (z₂.im -  z₁.im))*((-(z₂.re - z₁.re) * Real.sqrt (3)) + (z₂.im - z₁.im))) := by{
          exact Real.sqrt_mul (mul_self_nonneg (1/2)) (((z₂.re - z₁.re) + (Real.sqrt (3) * (z₂.im - z₁.im)))*((z₂.re - z₁.re) +  (Real.sqrt (3) * (z₂.im - z₁.im))) + ((- (z₂.re - z₁.re) * Real.sqrt (3)) +  (z₂.im -  z₁.im))*((-(z₂.re - z₁.re) * Real.sqrt (3)) + (z₂.im - z₁.im)))
        }
        _= Real.sqrt ((1/2) * (1/2)) * Real.sqrt ((a + b)*(a + b) + (c + d)*(c + d)) := by exact rfl
        _= Real.sqrt ((1/2) * (1/2)) * Real.sqrt (a*a + 2*a*b + b*b + c*c + 2*c*d + d*d) := by ring
        _= Real.sqrt ((1/2) * (1/2)) * Real.sqrt ((z₂.re - z₁.re) * (z₂.re - z₁.re) + 2* (z₂.re - z₁.re) * ( Real.sqrt (3) * (z₂.im - z₁.im)) + ( Real.sqrt (3) * (z₂.im - z₁.im)) * ( Real.sqrt (3) * (z₂.im - z₁.im)) + (- (z₂.re - z₁.re) * Real.sqrt (3)) * (- (z₂.re - z₁.re) * Real.sqrt (3)) + 2* (- (z₂.re - z₁.re) * Real.sqrt (3)) * (z₂.im - z₁.im) + (z₂.im - z₁.im) * (z₂.im - z₁.im)) := by exact rfl
        _= Real.sqrt ((1/2) * (1/2)) * Real.sqrt (a*a + b*b + c*c + d*d) := by ring
        _= Real.sqrt ((1/2) * (1/2)) * Real.sqrt ( (z₂.re - z₁.re) * (z₂.re - z₁.re) + (Real.sqrt (3) * (z₂.im - z₁.im)) * (Real.sqrt (3) * (z₂.im - z₁.im)) + (- (z₂.re - z₁.re) * Real.sqrt (3)) * (- (z₂.re - z₁.re) * Real.sqrt (3)) + (z₂.im - z₁.im) * (z₂.im - z₁.im)) := by exact rfl
        _= Real.sqrt ((1/2) * (1/2)) * Real.sqrt ( (z₂.re - z₁.re) * (z₂.re - z₁.re) + (Real.sqrt (3)* Real.sqrt (3) * (z₂.im - z₁.im) * (z₂.im - z₁.im)) + (((z₂.re - z₁.re))  * ((z₂.re - z₁.re) * Real.sqrt (3) * Real.sqrt (3)) + (z₂.im - z₁.im) * (z₂.im - z₁.im))) := by ring
        _= Real.sqrt ((1/2) * (1/2)) * Real.sqrt ( (z₂.re - z₁.re) * (z₂.re - z₁.re) + (3 * (z₂.im - z₁.im) * (z₂.im - z₁.im)) + (((z₂.re - z₁.re))  * ((z₂.re - z₁.re) * Real.sqrt (3) * Real.sqrt (3)) + (z₂.im - z₁.im) * (z₂.im - z₁.im)))  := by {
          have : Real.sqrt (3)* Real.sqrt (3) = 3 := by {
            norm_num
          }
          rw [this]
        }
        _= Real.sqrt ((1/2) * (1/2)) * Real.sqrt ( (z₂.re - z₁.re) * (z₂.re - z₁.re) + 3 * ((z₂.im - z₁.im) * (z₂.im - z₁.im)) + Real.sqrt (3) * Real.sqrt (3) * (((z₂.re - z₁.re))  * (z₂.re - z₁.re)) + (z₂.im - z₁.im) * (z₂.im - z₁.im)) := by ring
        _= Real.sqrt ((1/2) * (1/2)) * Real.sqrt ( (z₂.re - z₁.re) * (z₂.re - z₁.re) + 3 * ((z₂.im - z₁.im) * (z₂.im - z₁.im)) + 3 * (((z₂.re - z₁.re))  * (z₂.re - z₁.re)) + (z₂.im - z₁.im) * (z₂.im - z₁.im)) := by {
          have : Real.sqrt (3)* Real.sqrt (3) = 3 := by {
            norm_num
          }
          rw [this]
        }
        _= Real.sqrt ((1/2) * (1/2)) * Real.sqrt ( (a*a) + 3 * (d * d) + 3 * (a * a) + (d * d) ):= by exact rfl
        _= Real.sqrt ((1/2) * (1/2)) * Real.sqrt ( (2*2) * (a*a + d * d) ):= by ring
        _= Real.sqrt ((1/2) * (1/2)) * Real.sqrt (2 *2) * Real.sqrt ( a*a + d * d ):= by {
          rw [Real.sqrt_mul (mul_self_nonneg (2)) (a*a + d * d)]
          ring
        }
        _= Real.sqrt ((1/2) * (1/2)) * Real.sqrt (2 *2) * Real.sqrt ( (z₂.re - z₁.re) * (z₂.re - z₁.re) + (z₂.im - z₁.im) * (z₂.im - z₁.im) ):= by exact rfl
        _= Real.sqrt ((1/2) * (1/2) * 2 * 2) * Real.sqrt ( (z₂.re - z₁.re) * (z₂.re - z₁.re) + (z₂.im - z₁.im) * (z₂.im - z₁.im) ):= by norm_num
        _= Real.sqrt (1) * Real.sqrt ( (z₂.re - z₁.re) * (z₂.re - z₁.re) + (z₂.im - z₁.im) * (z₂.im - z₁.im) ):= by norm_num
        _= Real.sqrt ( (z₂.re - z₁.re) * (z₂.re - z₁.re) + (z₂.im - z₁.im) * (z₂.im - z₁.im) ):= by norm_num
        _= Complex.abs ⟨z₂.re - z₁.re, z₂.im - z₁.im⟩ := by exact rfl
        _= Complex.abs (⟨z₂.re, z₂.im⟩ - ⟨z₁.re, z₁.im⟩)  := by exact rfl
        _= Complex.abs (z₂ - z₁) := by exact rfl
        _= c1.radius := by exact rfl
      · calc Complex.abs (s₁ - z₂) = Complex.abs (⟨x₁,y₁⟩ - ⟨z₂.re, z₂.im⟩) := by exact rfl
        _= Complex.abs ⟨x₁ - z₂.re, y₁ - z₂.im⟩ := by exact rfl
        _= Complex.abs ⟨(1/2) * (z₁.re + z₂.re - Real.sqrt (3) * (z₁.im -z₂.im)) - z₂.re, (1/ 2) * ((z₁.re - z₂.re) * Real.sqrt (3) + (z₁.im + z₂.im)) - z₂.im⟩ := by exact rfl
        _= Complex.abs ⟨(-1/2) * (z₂.re - z₁.re) + (1/2) * Real.sqrt (3) * (z₂.im - z₁.im), -(1/2) * (z₂.re - z₁.re) * Real.sqrt (3) - (1/2) * (z₂.im -  z₁.im)⟩ := by ring
        _= Real.sqrt (((-1/2) * (z₂.re - z₁.re) + (1/2) * Real.sqrt (3) * (z₂.im - z₁.im))*((-1/2) * (z₂.re - z₁.re) + (1/2) * Real.sqrt (3) * (z₂.im - z₁.im)) + (-(1/2) * (z₂.re - z₁.re) * Real.sqrt (3) - (1/2) * (z₂.im -  z₁.im))*(-(1/2) * (z₂.re - z₁.re) * Real.sqrt (3) - (1/2) * (z₂.im -  z₁.im))) := by exact rfl
        _= Real.sqrt (((-1/2) * (-1/2) * (((z₂.re - z₁.re) - Real.sqrt (3) * (z₂.im - z₁.im))*((z₂.re - z₁.re) -  Real.sqrt (3) * (z₂.im - z₁.im)) + ((z₂.re - z₁.re) * Real.sqrt (3) + (z₂.im -  z₁.im))*((z₂.re - z₁.re) * Real.sqrt (3) + (z₂.im - z₁.im))))):= by ring
        _= Real.sqrt ((-1/2) * (-1/2)) * Real.sqrt (((z₂.re - z₁.re) - (Real.sqrt (3) * (z₂.im - z₁.im)))*((z₂.re - z₁.re) -  (Real.sqrt (3) * (z₂.im - z₁.im))) + ((z₂.re - z₁.re) * Real.sqrt (3) + (z₂.im -  z₁.im))*((z₂.re - z₁.re) * Real.sqrt (3) + (z₂.im - z₁.im))):= by {
          exact Real.sqrt_mul (mul_self_nonneg (-1/2)) (((z₂.re - z₁.re) - (Real.sqrt (3) * (z₂.im - z₁.im)))*((z₂.re - z₁.re) -  (Real.sqrt (3) * (z₂.im - z₁.im))) + ((z₂.re - z₁.re) * Real.sqrt (3) + (z₂.im -  z₁.im))*((z₂.re - z₁.re) * Real.sqrt (3) + (z₂.im - z₁.im)))
        }
        _= Real.sqrt ((-1/2) * (-1/2)) * Real.sqrt (((z₂.re - z₁.re) - (Real.sqrt (3) * (z₂.im - z₁.im)))*((z₂.re - z₁.re) -  (Real.sqrt (3) * (z₂.im - z₁.im))) + ((z₂.re - z₁.re) * Real.sqrt (3) + (z₂.im -  z₁.im))*((z₂.re - z₁.re) * Real.sqrt (3) + (z₂.im - z₁.im))) := by ring
        _= Real.sqrt ((-1/2) * (-1/2)) * Real.sqrt ((a - Real.sqrt (3) * d) * (a - Real.sqrt (3) * d) + (a * Real.sqrt (3) + d)*(a * Real.sqrt (3) + d)) := by exact rfl
        _= Real.sqrt ((-1/2) * (-1/2)) * Real.sqrt ( a*a - 2*a*Real.sqrt (3) * d + Real.sqrt (3) * Real.sqrt (3) * d*d + a*a *Real.sqrt (3) *Real.sqrt (3) + 2*a*Real.sqrt (3) * d + d*d) := by ring
        _= Real.sqrt ((-1/2) * (-1/2)) * Real.sqrt ( a*a - 2*a*Real.sqrt (3) * d + 3 * d*d + a*a * Real.sqrt (3) * Real.sqrt (3) + 2*a*Real.sqrt (3) * d + d*d) := by {
          have : Real.sqrt (3) * Real.sqrt (3) = 3 := by {
            norm_num
          }
          rw [this]
        }
        _= Real.sqrt ((-1/2) * (-1/2)) * Real.sqrt ( a*a - 2*a*Real.sqrt (3) * d + 3 * d*d + (Real.sqrt (3) * Real.sqrt (3) * a*a  + 2*a*Real.sqrt (3) * d + d*d) ) := by ring
        _= Real.sqrt ((-1/2) * (-1/2)) * Real.sqrt ( a*a + 3 * d*d + a*a *3 + d*d) := by {
          have : Real.sqrt (3) * Real.sqrt (3) = 3 := by {
            norm_num
          }
          rw [this]
          ring
        }
        _= Real.sqrt ((-1/2) * (-1/2)) * Real.sqrt ( (2*2) * (a*a + d*d)) := by ring
        _= Real.sqrt ((-1/2) * (-1/2)) * Real.sqrt (2 *2) * Real.sqrt ( a*a + d*d) := by {
          rw [Real.sqrt_mul (mul_self_nonneg (2)) (a*a + d*d)]
          ring
        }
        _= Real.sqrt ((-1/2) * (-1/2) * 2 * 2) * Real.sqrt ( a*a + d*d) := by norm_num
        _= Real.sqrt (1) * Real.sqrt ( a*a + d*d) := by norm_num
        _= Real.sqrt ( a*a + d*d) := by norm_num
        _= Complex.abs ⟨z₂.re - z₁.re, z₂.im - z₁.im⟩ := by exact rfl
        _= Complex.abs (⟨z₂.re, z₂.im⟩ - ⟨z₁.re, z₁.im⟩)  := by exact rfl
        _= Complex.abs (z₂ - z₁) := by exact rfl
        _= c2.radius := by exact rfl

    }
    have hs₁' : s₁ ∈ constructible_numbers M (h0) (h1) := by{
      exact element_circle_circle_intersection_constructible M h0 h1 c1 c2 hc₁ hc₂ hcc s₁ hs₁
    }
    have hs₂ : s₂ ∈ c1.points ∩ c2.points := by{

      let a : ℝ :=  (z₂.re - z₁.re)
      let b : ℝ :=  (z₂.im - z₁.im)
      constructor
      · calc Complex.abs (s₂ - z₁) = Complex.abs (⟨x₂,y₂⟩ - ⟨z₁.re, z₁.im⟩) := by exact rfl
        _= Complex.abs ⟨x₂ - z₁.re, y₂ - z₁.im⟩ := by exact rfl
        _= Complex.abs ⟨(1/2) * (z₁.re + z₂.re + Real.sqrt (3) * (z₁.im -z₂.im)) - z₁.re, (1/ 2) * ((z₂.re - z₁.re) * Real.sqrt (3) + (z₁.im + z₂.im)) - z₁.im⟩ := by exact rfl
        _= Complex.abs ⟨(1/2) * ((z₂.re - z₁.re) -  Real.sqrt (3) * (z₂.im -z₁.im)), (1/2) * ((z₂.re - z₁.re) * Real.sqrt (3) + (z₂.im - z₁.im))⟩ := by ring
        _= Complex.abs ⟨(1/2) * ((a - Real.sqrt (3) * b)), (1/2) * (a * Real.sqrt (3) + b)⟩ := by exact rfl
        _= Real.sqrt (((1/2) * ((a - Real.sqrt (3) * b)))*((1/2) * ((a - Real.sqrt (3) * b))) + ((1/2) * (a * Real.sqrt (3) + b))*((1/2) * (a * Real.sqrt (3) + b))) := by exact rfl
        _= Real.sqrt ((1/2) * (1/2) * (((a - Real.sqrt (3) * b))*((a - Real.sqrt (3) * b)) + (a * Real.sqrt (3) + b)*(a * Real.sqrt (3) + b))) := by ring
        _= Real.sqrt ((1/2) * (1/2)) * Real.sqrt (((a - Real.sqrt (3) * b))*((a - Real.sqrt (3) * b)) + (a * Real.sqrt (3) + b)*(a * Real.sqrt (3) + b)) := by {
          exact Real.sqrt_mul (mul_self_nonneg (1/2)) (((a - Real.sqrt (3) * b))*((a - Real.sqrt (3) * b)) + (a * Real.sqrt (3) + b)*(a * Real.sqrt (3) + b))
        }
        _= Real.sqrt ((1/2) * (1/2)) * Real.sqrt ((a*a - 2*a*Real.sqrt (3) * b + Real.sqrt (3) * Real.sqrt (3) * b*b + a*a *Real.sqrt (3) *Real.sqrt (3) + 2*a*Real.sqrt (3) * b + b*b)) := by ring
        _= Real.sqrt ((1/2) * (1/2)) * Real.sqrt ((a*a - 2*a*Real.sqrt (3) * b + 3 * b*b + a*a * Real.sqrt (3) * Real.sqrt (3) + 2*a*Real.sqrt (3) * b + b*b)) := by {
          have : Real.sqrt (3) * Real.sqrt (3) = 3 := by {
            norm_num
          }
          rw [this]
        }
        _= Real.sqrt ((1/2) * (1/2)) * Real.sqrt ((a*a - 2*a*Real.sqrt (3) * b + 3 * b*b + (Real.sqrt (3) * Real.sqrt (3) * a*a  + 2*a*Real.sqrt (3) * b + b*b) )) := by ring
        _= Real.sqrt ((1/2) * (1/2)) * Real.sqrt ((a*a + 3 * b*b + a*a *3 + b*b)) := by {
          have : Real.sqrt (3) * Real.sqrt (3) = 3 := by {
            norm_num
          }
          rw [this]
          ring
        }
        _= Real.sqrt ((1/2) * (1/2)) * Real.sqrt ( (2*2) * (a*a + b*b)) := by ring
        _= Real.sqrt ((1/2) * (1/2)) * Real.sqrt (2 *2) * Real.sqrt ( a*a + b*b) := by {
          rw [Real.sqrt_mul (mul_self_nonneg (2)) (a*a + b*b)]
          ring
        }
        _= Real.sqrt ((1/2) * (1/2) * 2 * 2) * Real.sqrt ( a*a + b*b) := by norm_num
        _= Real.sqrt (1) * Real.sqrt ( a*a + b*b) := by norm_num
        _= Real.sqrt ( a*a + b*b) := by norm_num
        _= Complex.abs ⟨z₂.re - z₁.re, z₂.im - z₁.im⟩ := by exact rfl
        _= Complex.abs (⟨z₂.re, z₂.im⟩ - ⟨z₁.re, z₁.im⟩)  := by exact rfl
        _= Complex.abs (z₂ - z₁) := by exact rfl
        _= c1.radius := by exact rfl

      · calc Complex.abs (s₂ - z₂) = Complex.abs (⟨x₂,y₂⟩ - ⟨z₂.re, z₂.im⟩) := by exact rfl
        _= Complex.abs ⟨x₂ - z₂.re, y₂ - z₂.im⟩ := by exact rfl
        _= Complex.abs ⟨(1/2) * (z₁.re + z₂.re + Real.sqrt (3) * (z₁.im -z₂.im)) - z₂.re, (1/ 2) * ((z₂.re - z₁.re) * Real.sqrt (3) + (z₁.im + z₂.im)) - z₂.im⟩ := by exact rfl
        _= Complex.abs ⟨(-1/2) * ((z₂.re - z₁.re) +  Real.sqrt (3) * (z₂.im -z₁.im)), (-1/2) * (-(z₂.re - z₁.re) * Real.sqrt (3) + (z₂.im - z₁.im))⟩ := by ring
        _= Complex.abs ⟨(-1/2) * (a + Real.sqrt (3) * b), (-1/2) * (-a * Real.sqrt (3) + b)⟩ := by exact rfl
        _= Real.sqrt (((-1/2) * (a + Real.sqrt (3) * b))*((-1/2) * (a + Real.sqrt (3) * b)) + ((-1/2) * (-a * Real.sqrt (3) + b))*((-1/2) * (-a * Real.sqrt (3) + b))) := by exact rfl
        _= Real.sqrt ((-1/2) * (-1/2) * (((a + Real.sqrt (3) * b))*((a + Real.sqrt (3) * b)) + ((-a * Real.sqrt (3) + b))*(-a * Real.sqrt (3) + b))) := by ring
        _= Real.sqrt ((-1/2) * (-1/2)) * Real.sqrt (((a + Real.sqrt (3) * b))*((a + Real.sqrt (3) * b)) + ((-a * Real.sqrt (3) + b))*(-a * Real.sqrt (3) + b)) := by {
          exact Real.sqrt_mul (mul_self_nonneg (-1/2)) (((a + Real.sqrt (3) * b))*((a + Real.sqrt (3) * b)) + ((-a * Real.sqrt (3) + b))*(-a * Real.sqrt (3) + b))
        }
        _= Real.sqrt ((-1/2) * (-1/2)) * Real.sqrt ((a*a + 2*a*Real.sqrt (3) * b + Real.sqrt (3) * Real.sqrt (3) * b*b + a*a *Real.sqrt (3) *Real.sqrt (3) + -2*a*Real.sqrt (3) * b + b*b)) := by ring
        _= Real.sqrt ((-1/2) * (-1/2)) * Real.sqrt ((a*a + 2*a*Real.sqrt (3) * b + 3 * b*b + a*a * Real.sqrt (3) * Real.sqrt (3) + -2*a*Real.sqrt (3) * b + b*b)) := by {
          have : Real.sqrt (3) * Real.sqrt (3) = 3 := by {
            norm_num
          }
          rw [this]
        }
        _= Real.sqrt ((-1/2) * (-1/2)) * Real.sqrt ((a*a + 2*a*Real.sqrt (3) * b + 3 * b*b + (Real.sqrt (3) * Real.sqrt (3) * a*a  + -2*a*Real.sqrt (3) * b + b*b) )) := by ring
        _= Real.sqrt ((-1/2) * (-1/2)) * Real.sqrt ((a*a + 3 * b*b + a*a *3 + b*b)) := by {
          have : Real.sqrt (3) * Real.sqrt (3) = 3 := by {
            norm_num
          }
          rw [this]
          ring
        }
        _= Real.sqrt ((-1/2) * (-1/2)) * Real.sqrt ( (2*2) * (a*a + b*b)) := by ring
        _= Real.sqrt ((-1/2) * (-1/2)) * Real.sqrt (2 *2) * Real.sqrt ( a*a + b*b) := by {
          rw [Real.sqrt_mul (mul_self_nonneg (2)) (a*a + b*b)]
          ring
        }
        _= Real.sqrt ((-1/2) * (-1/2) * 2 * 2) * Real.sqrt ( a*a + b*b) := by norm_num
        _= Real.sqrt (1) * Real.sqrt ( a*a + b*b) := by norm_num
        _= Real.sqrt ( a*a + b*b) := by norm_num
        _= Complex.abs ⟨z₂.re - z₁.re, z₂.im - z₁.im⟩ := by exact rfl
        _= Complex.abs (⟨z₂.re, z₂.im⟩ - ⟨z₁.re, z₁.im⟩)  := by exact rfl
        _= Complex.abs (z₂ - z₁) := by exact rfl
        _= c2.radius := by exact rfl

    }
    have hs₂' : s₂ ∈ constructible_numbers M (h0) (h1) := by{
      exact element_circle_circle_intersection_constructible M h0 h1 c1 c2 hc₁ hc₂ hcc s₂ hs₂
    }
    let L1 : line_through_two_points := {z₁ := z₁, z₂ := z₂}
    let L2 : line_through_two_points := {z₁ := s₁, z₂ := s₂}
    have hL1 : L1 ∈ constructible_lines (constructible_numbers M (h0) (h1)) := by{
      use z₁
      use z₂
    }
    have hL2 : L2 ∈ constructible_lines (constructible_numbers M (h0) (h1)) := by{
      use s₁
      use s₂
    }
    have hll: L1.points ≠ L2.points := by{
      have hll₁: z₁ ∈ L1.points := by exact line_through_two_points_beginn_in_points L1
      have hll₂: z₁ ∉ L2.points := by{
        unfold line_through_two_points.points
        simp
        intro t
        ring
        intro hsmth
        ring at hsmth
        simp at hsmth
        have : z₁ = z₂ := by {
            have ht : z₁ = t* s₁ + (1 - t) * s₂ := by {
              simp [hsmth]
              ring
              simp
              exact id hsmth.symm
            }
            have hzz: z₁ = s₂ + t * (s₁ - s₂) := by {
              rw [ht]
              ring
            }
            have hzz' : z₁ = s₂ + t * ⟨- Real.sqrt 3  * (z₁.im - z₂.im),Real.sqrt 3 * ( z₁.re -z₂.re)⟩  := by {
              calc z₁ = s₂ + (t : ℂ) * (s₁ - s₂) := by exact hzz
              _= s₂ + t * (⟨1/2 * (z₁.re + z₂.re - Real.sqrt 3 * (z₁.im - z₂.im)), 1/2 * ((z₁.re - z₂.re) * Real.sqrt 3 + (z₁.im + z₂.im))⟩ - ⟨1/2 * (z₁.re + z₂.re + Real.sqrt 3 * (z₁.im - z₂.im)), 1/2 * ((z₂.re - z₁.re) * Real.sqrt 3 + (z₁.im + z₂.im))⟩) := by simp
              _= s₂ + t * (⟨1/2 * (z₁.re + z₂.re - Real.sqrt 3 * (z₁.im - z₂.im)), 1/2 * ((z₁.re - z₂.re) * Real.sqrt 3 + (z₁.im + z₂.im))⟩ - ⟨1/2 * (z₁.re + z₂.re + Real.sqrt 3 * (z₁.im - z₂.im)), 1/2 * ((z₂.re - z₁.re) * Real.sqrt 3 + (z₁.im + z₂.im))⟩) := by ring
              _= s₂ + t * ⟨1/2 * (z₁.re + z₂.re - Real.sqrt 3 * (z₁.im - z₂.im)) - 1/2 * (z₁.re + z₂.re + Real.sqrt 3 * (z₁.im - z₂.im)), 1/2 * ((z₁.re - z₂.re) * Real.sqrt 3 + (z₁.im + z₂.im)) - 1/2 * ((z₂.re - z₁.re) * Real.sqrt 3 + (z₁.im + z₂.im))⟩ := by exact rfl
              _= s₂ + t * ⟨- Real.sqrt 3 * (z₁.im - z₂.im), Real.sqrt 3 * (z₁.re - z₂.re)⟩ := by ring
              _= s₂ + (t : ℂ ) * ⟨- Real.sqrt 3 * (z₁.im - z₂.im), Real.sqrt 3 * (z₁.re - z₂.re)⟩ := by simp
            }
            have ht₁: t = 1/2 * (z₁.re -z₂.re - Real.sqrt 3 * (z₁.im - z₂.im)) / (Real.sqrt 3 * (z₂.im - z₁.im)) := by{
              apply_fun Complex.re at hzz'
              simp at hzz'
              apply_fun (fun x ↦ x - 2⁻¹ * (z₁.re + z₂.re + Real.sqrt 3 * (z₁.im - z₂.im))) at hzz'
              simp at hzz'
              have hn0: -(Real.sqrt 3 * (z₁.im -z₂.im)) ≠ 0 := by {
                have : z₁.im -z₂.im ≠ 0 := by {
                  intro hyp
                  have : z₁.im = z₂.im := by {
                    apply_fun (fun x ↦ x + z₂.im) at hyp
                    ring at hyp
                    exact hyp
                  }
                  exact h this
                }
                simp [this]
              }
              apply_fun (fun x ↦ x / -(Real.sqrt 3 * (z₁.im - z₂.im))) at hzz'
              have : -(t * (Real.sqrt 3 * (z₁.im  - z₂.im))) / - (Real.sqrt 3 * (z₁.im - z₂.im)) = t := by {
                field_simp
              }
              rw [this] at hzz'
              calc t = (z₁.re - 2⁻¹ * (z₁.re + z₂.re + Real.sqrt 3 * (z₁.im - z₂.im))) / -(Real.sqrt 3 * (z₁.im - z₂.im)) := by exact id hzz'.symm
              _= 1/2 * (z₁.re - z₂.re - Real.sqrt 3 * (z₁.im - z₂.im)) / (Real.sqrt 3 * (z₂.im - z₁.im)) := by ring
            }
            by_cases hrealnot0 : z₁.re - z₂.re = 0
            · have hrealnot0' : z₁.re = z₂.re := by {
                apply_fun (fun x ↦ x + z₂.re) at hrealnot0
                ring at hrealnot0
                exact hrealnot0
              }
              have hrealnot0'' : z₁.im = z₂.im := by {
                apply_fun Complex.im at hzz'
                simp [hrealnot0] at hzz'
                have : (z₂.re - z₁.re) = - (z₁.re - z₂.re) := by ring
                rw [this] at hzz'
                simp [hrealnot0] at hzz'
                apply_fun (fun x ↦ 2*x - z₁.im) at hzz'
                ring at hzz'
                exact hzz'
              }
              exact (h hrealnot0'').elim
            · have ht₂ : t = 1/2 * (z₁.im -z₂.im + Real.sqrt 3 * (z₁.re - z₂.re)) / (Real.sqrt 3 * (z₁.re - z₂.re)) := by{
                apply_fun Complex.im at hzz'
                simp at hzz'
                apply_fun (fun x ↦ x - 2⁻¹ * ((z₂.re - z₁.re) * Real.sqrt 3 + (z₁.im + z₂.im))) at hzz'
                ring at hzz'
                simp at hzz'
                have hn0: (Real.sqrt 3 * (z₁.re -z₂.re)) ≠ 0 := by {
                  simp [hrealnot0]
                }
                apply_fun (fun x ↦ x / (Real.sqrt 3 * (z₁.re - z₂.re))) at hzz'
                have : (-(z₂.re * Real.sqrt 3 * t) + z₁.re * Real.sqrt 3 * t) / (Real.sqrt 3 * (z₁.re - z₂.re)) = t := by {
                  field_simp
                  ring
                }
                rw [this] at hzz'
                have : (z₁.im * 2⁻¹ + -(z₂.re * Real.sqrt 3 * 2⁻¹) + z₁.re * Real.sqrt 3 * 2⁻¹ + -(z₂.im * 2⁻¹)) = 1/2 * (z₁.im -z₂.im + Real.sqrt 3 * (z₁.re - z₂.re)):= by{
                  ring
                }
                rw [this] at hzz'
                exact id hzz'.symm
              }
              have : 1 / 2 * (z₁.re - z₂.re - Real.sqrt 3 * (z₁.im - z₂.im)) / (Real.sqrt 3 * (z₂.im - z₁.im)) = 1 / 2 * (z₁.im - z₂.im + Real.sqrt 3 * (z₁.re - z₂.re)) / (Real.sqrt 3 * (z₁.re - z₂.re)) := by{
                rw [ht₁] at ht₂
                exact ht₂
              }
              apply_fun (fun x ↦ x * 2 * 1 / (Real.sqrt 3)) at this
              have hyp: (z₂.im - z₁.im) ≠ 0:=by{
                intro hyp
                have : z₁.im = z₂.im := by {
                  apply_fun (fun x ↦ x + z₁.im) at hyp
                  ring at hyp
                  exact id hyp.symm
                }
                exact h this
              }
              field_simp at this
              have hyp2 :  (z₁.re - z₂.re - Real.sqrt 3 * (z₁.im - z₂.im)) * 2 * (2 * (Real.sqrt 3 * (z₁.re - z₂.re)) * Real.sqrt 3) =
                            (z₁.re - z₂.re - Real.sqrt 3 * (z₁.im - z₂.im)) * 2 * 2 * 3 * (z₁.re - z₂.re) := by {
                calc (z₁.re - z₂.re - Real.sqrt 3 * (z₁.im - z₂.im)) * 2 * (2 * (Real.sqrt 3 * (z₁.re - z₂.re)) * Real.sqrt 3) = (z₁.re - z₂.re - Real.sqrt 3 * (z₁.im - z₂.im)) * 2 * 2 * (Real.sqrt 3 * Real.sqrt 3) * (z₁.re - z₂.re) := by ring
                _= (z₁.re - z₂.re - Real.sqrt 3 * (z₁.im - z₂.im)) * 2 * 2 * 3 * (z₁.re - z₂.re) := by {
                  have : Real.sqrt 3 * Real.sqrt 3 = 3 := by {
                    norm_num
                  }
                  rw [this]
                }
              }
              have hyp3 : (z₁.im - z₂.im + Real.sqrt 3 * (z₁.re - z₂.re)) * 2 * (2 * (Real.sqrt 3 * (z₂.im - z₁.im)) * Real.sqrt 3) =
                            (z₁.im - z₂.im + Real.sqrt 3 * (z₁.re - z₂.re)) * 2 * 2 * 3 * (z₂.im - z₁.im) := by {
                calc (z₁.im - z₂.im + Real.sqrt 3 * (z₁.re - z₂.re)) * 2 * (2 * (Real.sqrt 3 * (z₂.im - z₁.im)) * Real.sqrt 3) = (z₁.im - z₂.im + Real.sqrt 3 * (z₁.re - z₂.re)) * 2 * 2 * (Real.sqrt 3 * Real.sqrt 3) * (z₂.im - z₁.im) := by ring
                _= (z₁.im - z₂.im + Real.sqrt 3 * (z₁.re - z₂.re)) * 2 * 2 * 3 * (z₂.im - z₁.im) := by {
                  have : Real.sqrt 3 * Real.sqrt 3 = 3 := by {
                    norm_num
                  }
                  rw [this]
                }
              }
              rw [hyp2, hyp3] at this
              apply_fun (fun x ↦ x / (2 * 2 * 3)) at this
              have hyp4: (z₁.re - z₂.re - Real.sqrt 3 * (z₁.im - z₂.im)) * 2 * 2 * 3 * (z₁.re - z₂.re) / (2 * 2 * 3) = (z₁.re - z₂.re - Real.sqrt 3 * (z₁.im - z₂.im)) * (z₁.re - z₂.re) := by {
                field_simp
                ring
              }
              have hyp5 : (z₁.im - z₂.im + Real.sqrt 3 * (z₁.re - z₂.re)) * 2 * 2 * 3 * (z₂.im - z₁.im) / (2 * 2 * 3) = (z₁.im - z₂.im + Real.sqrt 3 * (z₁.re - z₂.re)) * (z₂.im - z₁.im) := by {
                field_simp
                ring
              }
              rw [hyp4, hyp5] at this
              ring at this
              apply_fun (fun x ↦ x + z₁.re * Real.sqrt 3 * z₁.im - z₁.re * Real.sqrt 3 * z₂.im - z₂.re * Real.sqrt 3 * z₁.im + z₂.re * Real.sqrt 3 * z₂.im) at this
              ring at this
              have hyp6 : -(z₁.re * z₂.re * (2:ℝ)) + z₁.re ^ 2 + z₂.re ^ 2  = (z₁.re - z₂.re) * (z₁.re - z₂.re) := by {
                ring
              }
              have hyp7 :z₁.im * z₂.im * (2:ℝ ) + (-z₁.im ^ 2 - z₂.im ^ 2) =  - (z₁.im - z₂.im) * (z₁.im - z₂.im) := by {
                ring
              }
              rw [hyp6, hyp7] at this
              apply_fun (fun x ↦x + (z₁.im -z₂.im) * (z₁.im - z₂.im)) at this
              apply_fun (fun x ↦ Real.sqrt x) at this
              have hyp8 : Real.sqrt ((z₁.re - z₂.re) * (z₁.re - z₂.re) + (z₁.im - z₂.im) * (z₁.im - z₂.im)) = Complex.abs (z₁ - z₂):= by {
                calc Real.sqrt ((z₁.re - z₂.re) * (z₁.re - z₂.re) + (z₁.im - z₂.im) * (z₁.im - z₂.im)) = Complex.abs (⟨z₁.re -z₂.re, z₁.im -z₂.im⟩) := by exact rfl
                _= Complex.abs (z₁ - z₂) := by exact rfl
              }
              rw [hyp8] at this
              ring at this
              simp at this
              exact this
          }
        exact h' this
        }
      intro hsmth2
      rw[hsmth2] at hll₁
      exact hll₂ hll₁
    }
    have h : (z₁ + z₂) /2  ∈ L1.points ∩ L2.points := by{
      simp
      constructor
      · use 1/2
        calc (1/2 : ℝ ) * L1.z₁ + (1 - (1/2 : ℝ ) ) * L1.z₂ = (1/2) * z₁ + (1 - (1/2)) * z₂ := by simp
        _= (1/2) * z₁ + (1/2) * z₂ := by norm_num
        _= (z₁ + z₂) / 2 := by ring
      · use 1/2
      -- had to start like this, somehow lean didnt manage to understand the notation i used above, i think because it was too slow after all these steps
        calc (1/2 : ℝ ) * ⟨2⁻¹ * (z₁.re + z₂.re - Real.sqrt 3 * (z₁.im - z₂.im)), 2⁻¹ * ((z₁.re - z₂.re) * Real.sqrt 3 + (z₁.im + z₂.im)) ⟩ + (1 - (1/2 : ℝ)) * ⟨2⁻¹ * (z₁.re + z₂.re + Real.sqrt 3 * (z₁.im - z₂.im)), 2⁻¹ * ((z₂.re - z₁.re) * Real.sqrt (3) + (z₁.im + z₂.im))⟩ =  (1/2 : ℝ) * L2.z₁ + (1 - (1/2 : ℝ ) ) * L2.z₂  := by simp
        _= (1/2) * s₁ + (1 - (1/2)) * s₂ := by simp
        _= (1/2) * s₁ + (1/2) * s₂ := by norm_num
        _= (1/2) * (s₁ + s₂) := by ring
        _= (1/2) * (⟨x₁, y₁⟩ + ⟨x₂, y₂⟩) := by exact rfl
        _= (1/2) * ⟨(1/2) * (z₁.re + z₂.re - Real.sqrt (3) * (z₁.im -z₂.im)) + (1/2) * (z₁.re + z₂.re + Real.sqrt (3) * (z₁.im -z₂.im)), (1/ 2) * ((z₁.re - z₂.re) * Real.sqrt (3) + (z₁.im + z₂.im)) + (1/ 2) * ((z₂.re - z₁.re) * Real.sqrt (3) + (z₁.im + z₂.im))⟩ := by exact rfl
        _= (1/2) * ⟨z₁.re + z₂.re, z₁.im + z₂.im⟩ := by ring
        _= (1/2) * (z₁ + z₂) := by exact rfl
        _= (z₁ + z₂) / 2 := by ring
    }
    exact element_line_line_intersection_constructible M h0 h1 L1 L2 hL1 hL2 ((z₁ + z₂) /2) hll h

}
--needed for arbitrary multiplication. In this case angles are interpreted as e^(i*angle)
lemma constructible_numbers_add_angles (M: Set ℂ) (h0 : 0 ∈ M) (h1: 1 ∈ M) (a b : ℝ) (ha: Complex.exp (Complex.I* a) ∈ constructible_numbers M (h0) (h1)) (hb:  Complex.exp (Complex.I* b) ∈ constructible_numbers M (h0) (h1)):
  Complex.exp (Complex.I* (a+b)) ∈ constructible_numbers M (h0) (h1) := by{
    let C1 : circle_with_radius := {center := 0, radius := 1}
    have hc1 : C1 ∈ constructible_circles (constructible_numbers M (h0) (h1)) := by{
      use 0
      use 1
      use 0
      simp
      constructor
      · exact constructible_numbers_element_of M h0 h1 0 h0
      · constructor
        · exact constructible_numbers_element_of M h0 h1 1 h1
        · exact constructible_numbers_element_of M h0 h1 0 h0
    }
    let C2 : circle_with_radius := {center := Complex.exp (Complex.I * a), radius := Complex.abs (1 - Complex.exp (Complex.I* b))}
    have hc2: C2 ∈ constructible_circles (constructible_numbers M (h0) (h1)) := by{
      use Complex.exp (Complex.I * a)
      use Complex.abs 1
      use  Complex.exp (Complex.I* b)
      simp
      constructor
      · exact ha
      · constructor
        · exact constructible_numbers_element_of M h0 h1 1 h1
        · exact hb
    }
    have hcc : C1 ≠ C2 := by{
      have : Complex.exp (Complex.I * a) ≠ 0 := by {
        exact Complex.exp_ne_zero (Complex.I * (a : ℂ))
      }
      simp
      intro hcc'
      exact (this (id hcc'.symm)).elim
    }
    let z : ℂ := Complex.exp (Complex.I * (a+b))
    have hz : z ∈ C1.points ∩ C2.points := by{
      simp
      constructor
      · calc Complex.abs (z - 0) = Complex.abs z := by simp
        _= Complex.abs (Complex.exp (Complex.I * (a+b))) := by exact rfl
        _= Complex.abs (Complex.exp (Complex.I * a + Complex.I * b)) := by ring
        _= Complex.abs (Complex.exp (Complex.I * a) * Complex.exp (Complex.I * b)) := by rw[Complex.exp_add (Complex.I * a) (Complex.I * b)]
        _= Complex.abs (Complex.exp (Complex.I * a)) * Complex.abs (Complex.exp (Complex.I * b)) := by rw [@AbsoluteValue.map_mul]
        _= 1 * Complex.abs (Complex.exp (Complex.I * b)) := by {
          rw [Complex.abs_exp (Complex.I * a)]
          simp
        }
        _= Complex.abs (Complex.exp (Complex.I * b)) := by simp
        _= 1 := by {
          rw [Complex.abs_exp (Complex.I * b)]
          simp
        }
        _= C1.radius := by exact rfl
      · calc Complex.abs (z - Complex.exp (Complex.I * a)) = Complex.abs (Complex.exp (Complex.I * (a+b)) - Complex.exp (Complex.I * a)) := by exact rfl
        _= Complex.abs (Complex.exp (Complex.I * a + Complex.I * b) - Complex.exp (Complex.I * a)) := by ring
        _= Complex.abs (Complex.exp (Complex.I * a) * Complex.exp (Complex.I * b) - Complex.exp (Complex.I * a)) := by rw[Complex.exp_add (Complex.I * a) (Complex.I * b)]
        _= Complex.abs (Complex.exp (Complex.I *a) * (Complex.exp (Complex.I *b) - 1)) := by ring
        _= Complex.abs (Complex.exp (Complex.I *a)) * Complex.abs (Complex.exp (Complex.I *b) - 1) := by rw [@AbsoluteValue.map_mul]
        _= 1 * Complex.abs (Complex.exp (Complex.I *b) - 1) := by {
          rw [Complex.abs_exp (Complex.I * a)]
          simp
        }
        _= Complex.abs (Complex.exp (Complex.I *b) - 1) := by simp
        _= Complex.abs (- (1 - Complex.exp (Complex.I *b))) := by ring
        _= Complex.abs (1 - Complex.exp (Complex.I *b)) := by rw [@AbsoluteValue.map_neg]
        _= C2.radius := by exact rfl
    }
    have hz' : z ∈ constructible_numbers M (h0) (h1) := by{
      exact element_circle_circle_intersection_constructible M h0 h1 C1 C2 hc1 hc2 hcc z hz
    }
    exact hz'
}

lemma constructible_numbers_from_coords (M : Set ℂ) (h0: 0 ∈ M) (h1: 1 ∈ M) (a b : ℝ) (ha: ⟨a, 0⟩ ∈ constructible_numbers M (h0) (h1)) (hb: ⟨b, 0⟩ ∈ constructible_numbers M (h0) (h1)): ⟨a, b⟩ ∈ constructible_numbers M (h0) (h1) := by{
  let ib : ℂ := ⟨0, b⟩
  let L : line_through_two_points := {z₁ := 0, z₂ := Complex.I}
  have hL : L ∈ constructible_lines (constructible_numbers M (h0) (h1)) := by{
    use 0
    use Complex.I
    simp
    constructor
    · exact constructible_numbers_element_of M h0 h1 0 h0
    · exact constructible_numbers_contains_I M h0 h1
  }
  let C : circle_with_radius := {center := 0, radius := Complex.abs ⟨b, 0⟩}
  have hC : C ∈ constructible_circles (constructible_numbers M (h0) (h1)) := by{
    use 0
    use ⟨b,0⟩
    use 0
    simp
    constructor
    · exact constructible_numbers_element_of M h0 h1 0 h0
    · constructor
      · exact hb
      · exact constructible_numbers_element_of M h0 h1 0 h0
  }
  have h : ib ∈ line_circle_intersection L C := by{
    constructor
    · use 1 - b
      calc (1 - b : ℝ ) * L.z₁ + (1 - (1 - b : ℝ ) ) * L.z₂ = (1 - b : ℝ ) * 0 + (1 - (1 - b : ℝ ) ) * Complex.I := by exact rfl
      _= (1 - b : ℝ ) * 0 + (1 - (1 - b : ℝ ) ) * Complex.I := by norm_num
      _= 0 + (1 - (1 - b : ℝ ) ) * Complex.I := by ring
      _= (1 + (- 1 + b )) * Complex.I := by simp
      _= b * Complex.I := by ring
      _= ⟨b * 0, b * 1⟩ := by {
        refine Complex.ext_iff.mpr ?_
        constructor
        · simp
        · simp
      }
      _= ⟨0, b⟩ := by simp
      _= ib := by exact rfl
    · simp
      calc Complex.abs (ib - 0) = Complex.abs ⟨0, b⟩ := by simp
      _= Real.sqrt (0*0 + b*b) := by exact rfl
      _= Real.sqrt (b*b + 0*0) := by norm_num
      _= Complex.abs ⟨b, 0⟩ := by exact rfl
      _= C.radius := by exact rfl
  }
  have h5 : ib ∈ constructible_numbers M (h0) (h1) := by{
    exact element_line_circle_intersection_constructible M h0 h1 L C hL hC ib h
  }
  have h6 : ⟨a, 0⟩ + ib ∈ constructible_numbers M (h0) (h1) := by{
    exact constructible_numbers_closed_addition M h0 h1 ⟨a, 0⟩ ib ha h5
  }
  have h7 : ⟨a, b⟩ = ⟨a, 0⟩ + ib := by{
    refine Complex.ext_iff.mpr ?_
    constructor
    · simp
    · simp
  }
  rw [h7]
  exact h6
}

lemma constructible_numbers_contains_re (M: Set ℂ) (h0 : 0 ∈ M) (h1: 1 ∈ M) (z : ℂ) (hz: z ∈ constructible_numbers M (h0) (h1)):
  ⟨z.re,0⟩  ∈ constructible_numbers M (h0) (h1) := by{
  let zconj : ℂ := ⟨z.re, -z.im⟩
  have hzconj : zconj ∈ constructible_numbers M (h0) (h1) := by{
    exact constructible_numbers_closed_complex_conjugation M h0 h1 z hz
  }
  have hre : (z + zconj) / 2 ∈ constructible_numbers M (h0) (h1) := by{
    exact constructible_numbers_half_point M h0 h1 z zconj hz hzconj
  }
  have hre' : (z + zconj) / 2 = ⟨z.re, 0⟩ := by{
    refine Complex.ext_iff.mpr ?_
    constructor
    · simp
    · simp
  }
  exact Set.mem_of_eq_of_mem (id hre'.symm) hre
}

lemma constructible_numbers_contains_im (M: Set ℂ) (h0 : 0 ∈ M) (h1: 1 ∈ M) (z : ℂ) (hz: z ∈ constructible_numbers M (h0) (h1)):
  ⟨0,z.im⟩  ∈ constructible_numbers M (h0) (h1) := by{
  let x : ℂ := ⟨z.re, 0⟩
  have hx : x ∈ constructible_numbers M (h0) (h1) := by{
    exact constructible_numbers_contains_re M h0 h1 z hz
  }
  have hx1 : -x ∈ constructible_numbers M (h0) (h1) := by{
    exact constructible_numbers_additive_inverse M h0 h1 x hx
  }
  have hx2 : z + (- x) ∈ constructible_numbers M (h0) (h1) := by{
    exact constructible_numbers_closed_addition M h0 h1 z (-x) hz hx1
  }
  have hIm :  (z + (- x)) = ⟨0, z.im⟩  := by{
    calc (z + (- x)) = z + (- ⟨z.re, 0⟩) := by exact rfl
    _= z - ⟨z.re, 0⟩ := by ring
    _= ⟨z.re - z.re, z.im - 0⟩ := by exact rfl
    _= ⟨0, z.im⟩ := by ring
  }
  rw [←hIm]
  exact hx2
}

lemma constructible_numbers_contains_complex_iff_contains_coords (M : Set ℂ) (h0: 0 ∈ M) (h1: 1 ∈ M) (z : ℂ) (hz: z ∈ constructible_numbers M (h0) (h1)):
  z ∈ constructible_numbers M (h0) (h1) ↔ ⟨z.re, 0⟩ ∈ constructible_numbers M (h0) (h1) ∧ ⟨0, z.im⟩ ∈ constructible_numbers M (h0) (h1) := by{
  constructor
  · intro hz
    constructor
    · exact constructible_numbers_contains_re M h0 h1 z hz
    · exact constructible_numbers_contains_im M h0 h1 z hz
  · intro h
    have hz1 : z = ⟨z.re, 0⟩ + ⟨0, z.im⟩ := by{
      refine Complex.ext_iff.mpr ?_
      constructor
      · simp
      · simp
    }
    rw [hz1]
    exact constructible_numbers_closed_addition M h0 h1 ⟨z.re, 0⟩ ⟨0, z.im⟩ h.1 h.2
}
-- main work for containing multiplication of reals is here, for the general case below we just use this lemma in different cases
lemma constructible_numbers_multiplication_pos_reals_geq (M : Set ℂ) (h0 : 0 ∈ M) (h1: 1 ∈ M) (a b : ℝ) (ha1 : a > 0) (hb1: b > 0) (h: a ≥ b) (ha2: (a : ℂ )  ∈ constructible_numbers M (h0) (h1)) (hb2: (b : ℂ)  ∈ constructible_numbers M (h0) (h1)) :
((a*b : ℂ ) ) ∈ constructible_numbers M (h0) (h1) := by{
    have hbim : ⟨0, b⟩ ∈ constructible_numbers M (h0) (h1) := by{
      let b' : ℂ := ⟨b, b⟩
      have : b' ∈ constructible_numbers M (h0) (h1) := by{
        exact constructible_numbers_from_coords M h0 h1 b b hb2 hb2
      }
      exact constructible_numbers_contains_im M h0 h1 b' this
    }
    let b' : ℂ := ⟨1, b⟩
    have hb' : b' ∈ constructible_numbers M (h0) (h1) := by{
      have hb'' : 1 + ⟨0,b⟩ ∈ constructible_numbers M (h0) (h1) := by{
        exact constructible_numbers_closed_addition M h0 h1 1 ⟨0,b⟩ (constructible_numbers_element_of M h0 h1 1 h1) hbim
      }
      have : 1 + ⟨0,b⟩ = b' := by {
        refine Complex.ext_iff.mpr ?_
        constructor
        · simp
        · simp
      }
      exact Set.mem_of_eq_of_mem (id this.symm) hb''
    }
    let L1 : line_through_two_points := {z₁ := 0, z₂ := b'}
    have hL1 : L1 ∈ constructible_lines (constructible_numbers M (h0) (h1)) := by{
      use 0
      use b'
      simp
      constructor
      · exact constructible_numbers_element_of M h0 h1 0 h0
      · exact hb'
    }
    let I : ℂ := Complex.I
    have hI : I ∈ constructible_numbers M (h0) (h1) := by{
      exact constructible_numbers_contains_I M h0 h1
    }
    let L2 : line_through_two_points := {z₁ := a, z₂ := I + a}
    have hL2 : L2 ∈ constructible_lines (constructible_numbers M (h0) (h1)) := by{
      use a
      use I + a
      simp
      constructor
      · exact ha2
      · exact constructible_numbers_closed_addition M h0 h1 I a hI ha2
    }
    have hll : L1.points ≠ L2.points := by{
      have hll₁ : 0 ∈ L1.points := by{
        exact line_through_two_points_beginn_in_points L1
      }
      have hll₂ : 0 ∉ L2.points := by{
        unfold line_through_two_points.points
        simp
        intro x
        ring
        intro hsmth
        apply_fun Complex.re at hsmth
        simp at hsmth
        linarith
      }
      intro hsmth2
      rw[hsmth2] at hll₁
      exact hll₂ hll₁
    }
    let r : ℂ := ⟨a, a*b⟩
    have hr : r ∈ L1.points ∩ L2.points := by{
      simp
      constructor
      . use 1 - a
        calc (1 - a : ℝ ) * L1.z₁ + (1 - (1 - a : ℝ ) ) * L1.z₂ = (1 - a : ℝ ) * 0 + (1 - (1 - a : ℝ ) ) * b' := by exact rfl
        _= (1 - a : ℝ ) * 0 + (1 - (1 - a : ℝ ) ) * b' := by norm_num
        _= 0 + (1 - (1 - a : ℝ ) ) * b' := by ring
        _= (1 + (- 1 + a )) * b' := by simp
        _= a * b' := by ring
        _= ⟨a * 1, a * b⟩ := by {
          refine Complex.ext_iff.mpr ?_
          constructor
          · simp
          · simp
        }
        _= ⟨a, a*b⟩ := by simp
        _= r := by exact rfl
      . use 1 - a*b
        calc (1 - a*b : ℝ ) * L2.z₁ + (1 - (1 - a*b : ℝ ) ) * L2.z₂ = (1 - a*b : ℝ ) * a + (1 - (1 - a*b : ℝ ) ) * (I + a) := by exact rfl
        _= (1 - a*b : ℝ ) * a + (1 - (1 - a*b : ℝ ) ) * (I + a) := by norm_num
        _= (1 - a*b) * a + (1 - (1 - a*b)) * (I + a) := by simp
        _= a + (a*b) * I := by ring
        _= a + (a*b) * Complex.I := by exact rfl
        _= a + ⟨0, a*b⟩ := by {
          refine Complex.ext_iff.mpr ?_
          constructor
          · simp
          · simp
        }
        _= ⟨a + 0, (a*b)⟩ := by {
          refine Complex.ext_iff.mpr ?_
          constructor
          · simp
          · simp
        }
        _= ⟨a, (a*b)⟩ := by simp
        _= r := by exact rfl
    }
    have hr' : r ∈ constructible_numbers M (h0) (h1) := by{
      exact element_line_line_intersection_constructible M h0 h1 L1 L2 hL1 hL2 r hll hr
    }
    have hab :  ⟨0, a*b⟩ ∈ constructible_numbers M (h0) (h1) := by{
      exact constructible_numbers_contains_im M h0 h1 r hr'
    }
    have hab' : ⟨a*b, 0⟩ ∈ constructible_numbers M (h0) (h1) := by{
      let C : circle_with_radius := {center := 0, radius := Complex.abs (⟨0, a*b⟩) }
      let L : line_through_two_points := {z₁ := 0, z₂ := 1}
      have hC : C ∈ constructible_circles (constructible_numbers M (h0) (h1)) := by{
        use 0
        use ⟨0, a*b⟩
        use 0
        simp
        constructor
        · exact constructible_numbers_element_of M h0 h1 0 h0
        · constructor
          · exact hab
          · exact constructible_numbers_element_of M h0 h1 0 h0
      }
      have hL : L ∈ constructible_lines (constructible_numbers M (h0) (h1)) := by{
        use 0
        use 1
        simp
        constructor
        · exact constructible_numbers_element_of M h0 h1 0 h0
        · exact constructible_numbers_element_of M h0 h1 1 h1
      }
      have h : ⟨a*b, 0⟩ ∈ L.points ∩ C.points := by{
        simp
        constructor
        · use 1 - a*b
          calc (1 - a*b : ℝ ) * L.z₁ + (1 - (1 - a*b : ℝ ) ) * L.z₂ = (1 - a*b : ℝ ) * 0 + (1 - (1 - a*b : ℝ ) ) * 1 := by exact rfl
          _= (1 - a*b : ℝ ) * 0 + (1 - (1 - a*b : ℝ ) ) * 1 := by norm_num
          _= 0 + (1 - (1 - a*b : ℝ ) ) * 1 := by ring
          _= (1 + (- 1 + a*b )) * 1 := by simp
          _= a*b * 1 := by ring
          _= ⟨a*b * 1, a*b * 0⟩ := by {
            refine Complex.ext_iff.mpr ?_
            constructor
            · simp
            · simp
          }
          _= ⟨a*b, 0⟩ := by simp
          _= ⟨a*b, 0⟩ := by exact rfl
        · calc Complex.abs (⟨a*b, 0⟩ - 0) = Complex.abs ⟨a*b, 0⟩ := by simp
          _= Real.sqrt ((a*b)*(a*b) + 0*0) := by exact rfl
          _= Real.sqrt (0*0 + (a*b)*(a*b)) := by ring
          _= Complex.abs ⟨0, a*b⟩ := by exact rfl
          _= C.radius := by exact rfl
    }
      exact element_line_circle_intersection_constructible M h0 h1 L C hL hC ⟨a*b, 0⟩ h
    }
    have : (a*b : ℂ) = ⟨a*b, 0⟩ := by {
      refine Complex.ext_iff.mpr ?_
      constructor
      · simp
      · simp
    }
    rw [this]
    exact hab'
}

lemma constructible_numbers_multiplication_pos_reals (M : Set ℂ) (h0 : 0 ∈ M) (h1: 1 ∈ M) (a b : ℝ) (ha1 : a > 0) (hb1: b > 0) (ha2: (a : ℂ )  ∈ constructible_numbers M (h0) (h1)) (hb2: (b : ℂ)  ∈ constructible_numbers M (h0) (h1)) :
((a*b : ℂ ) ) ∈ constructible_numbers M (h0) (h1) := by{
  by_cases h : a ≥ b
  · exact constructible_numbers_multiplication_pos_reals_geq M h0 h1 a b ha1 hb1 h ha2 hb2
  · push_neg at h
    have : b ≥ a := by linarith
    rw [mul_comm]
    exact constructible_numbers_multiplication_pos_reals_geq M h0 h1 b a hb1 ha1 this hb2 ha2
}

lemma constructible_numbers_contains_abs (M: Set ℂ) (h0 : 0 ∈ M) (h1: 1 ∈ M) (z : ℂ) (hz: z ∈ constructible_numbers M (h0) (h1)):
  (Complex.abs z : ℂ  ) ∈ constructible_numbers M (h0) (h1) := by{
    let L : line_through_two_points := {z₁ := 0, z₂ := 1}
    have hL : L ∈ constructible_lines (constructible_numbers M (h0) (h1)) := by{
      use 0
      use 1
      simp
      constructor
      · exact constructible_numbers_element_of M h0 h1 0 h0
      · exact constructible_numbers_element_of M h0 h1 1 h1
    }
    let C : circle_with_radius := {center := 0, radius := Complex.abs z}
    have hC : C ∈ constructible_circles (constructible_numbers M (h0) (h1)) := by{
      use 0
      use z
      use 0
      simp
      constructor
      · exact constructible_numbers_element_of M h0 h1 0 h0
      · constructor
        · exact hz
        · exact constructible_numbers_element_of M h0 h1 0 h0
    }
    have hz' : (Complex.abs z : ℂ ) ∈ L.points ∩ C.points := by{
      simp
      constructor
      · use 1 - Complex.abs z
        calc (1 - Complex.abs z : ℝ ) * L.z₁ + (1 - (1 - Complex.abs z : ℝ ) ) * L.z₂ = (1 - Complex.abs z : ℝ ) * 0 + (1 - (1 - Complex.abs z : ℝ ) ) * 1 := by exact rfl
        _= (1 - Complex.abs z : ℝ ) * 0 + (1 - (1 - Complex.abs z : ℝ ) ) * 1 := by norm_num
        _= 0 + (1 - (1 - Complex.abs z : ℝ ) ) * 1 := by ring
        _= (1 + (- 1 + Complex.abs z )) * 1 := by simp
        _= Complex.abs z * 1 := by ring
        _= Complex.abs z := by simp
        _= (Complex.abs z : ℂ ) := by simp
      · calc Complex.abs ((Complex.abs z : ℂ ) - 0) = Complex.abs (Complex.abs z) := by simp
        _= Complex.abs (z) := by simp
        _= C.radius := by exact rfl
    }
    exact element_line_circle_intersection_constructible M h0 h1 L C hL hC (Complex.abs z : ℂ ) hz'
}

lemma construcible_numbers_contains_number_if_abs_and_arg (M :Set ℂ ) (h0 : 0 ∈ M) (h1 : 1 ∈ M) (z : ℂ) (hz: z ≠ 0 ) (harg: Complex.exp ((Complex.arg z : ℂ ) * Complex.I) ∈ constructible_numbers M (h0) (h1)) (habs: (Complex.abs z :ℂ)  ∈ constructible_numbers M h0 h1) : z ∈ constructible_numbers M h0 h1 := by{
  have hh: Complex.abs z > 0 := by{
    exact AbsoluteValue.pos Complex.abs hz
  }
  let L : line_through_two_points := {z₁ := 0, z₂ := Complex.exp ((Complex.arg z : ℂ ) * Complex.I) }
  have hL : L ∈ constructible_lines (constructible_numbers M (h0) (h1)) := by{
    use 0
    use Complex.exp ((Complex.arg z : ℂ ) * Complex.I)
    simp
    constructor
    · exact constructible_numbers_element_of M h0 h1 0 h0
    · exact harg
  }
  let C : circle_with_radius := {center := 0, radius := Complex.abs z}
  have hC : C ∈ constructible_circles (constructible_numbers M (h0) (h1)) := by{
    use 0
    use Complex.abs z
    use 0
    simp
    constructor
    · exact constructible_numbers_element_of M h0 h1 0 h0
    · constructor
      · exact habs
      · exact constructible_numbers_element_of M h0 h1 0 h0
  }
  have hz' : z ∈ L.points ∩ C.points := by{
    simp
    constructor
    · use 1 - Complex.abs z
      calc (1 - Complex.abs z : ℝ ) * L.z₁ + (1 - (1 - Complex.abs z : ℝ ) ) * L.z₂ = (1 - Complex.abs z : ℝ ) * 0 + (1 - (1 - Complex.abs z : ℝ ) ) * Complex.exp ((Complex.arg z : ℂ ) * Complex.I) := by exact rfl
      _= (1 - Complex.abs z : ℝ ) * 0 + (1 - (1 - Complex.abs z : ℝ ) ) * Complex.exp ((Complex.arg z : ℂ ) * Complex.I) := by norm_num
      _= 0 + (1 - (1 - Complex.abs z : ℝ ) ) * Complex.exp ((Complex.arg z : ℂ ) * Complex.I) := by ring
      _= (1 + (- 1 + Complex.abs z )) * Complex.exp ((Complex.arg z : ℂ ) * Complex.I) := by simp
      _= Complex.abs z * Complex.exp ((Complex.arg z : ℂ ) * Complex.I) := by ring
      _= (Complex.abs z : ℂ ) * Complex.exp ((Complex.arg z : ℂ ) * Complex.I) := by simp
      _= z := by simp
    · calc Complex.abs (z - 0) = Complex.abs z := by simp
      _= C.radius := by exact rfl
  }
  exact element_line_circle_intersection_constructible M h0 h1 L C hL hC z hz'
}

lemma constructible_numbers_contains_arg (M: Set ℂ) (h0 : 0 ∈ M) (h1: 1 ∈ M) (z : ℂ) (hz: z ∈ constructible_numbers M (h0) (h1)) (hz' : z ≠ 0):
  Complex.exp ((Complex.arg z : ℂ) * Complex.I)  ∈ constructible_numbers M (h0) (h1) := by{
    let L : line_through_two_points := {z₁ := 0, z₂ := z}
    have hL : L ∈ constructible_lines (constructible_numbers M (h0) (h1)) := by{
      use 0
      use z
      simp
      constructor
      · exact constructible_numbers_element_of M h0 h1 0 h0
      · exact hz
    }
    let C : circle_with_radius := {center := 0, radius := 1}
    have hC : C ∈ constructible_circles (constructible_numbers M (h0) (h1)) := by{
      use 0
      use 1
      use 0
      simp
      constructor
      · exact constructible_numbers_element_of M h0 h1 0 h0
      · constructor
        · exact constructible_numbers_element_of M h0 h1 1 h1
        · exact constructible_numbers_element_of M h0 h1 0 h0
    }
    have hz' : Complex.exp ((Complex.arg z : ℂ) * Complex.I ) ∈ L.points ∩ C.points := by{
      simp
      constructor
      · use 1 - 1 / Complex.abs z
        calc (1 - 1/Complex.abs z : ℝ) * L.z₁ + (1 - (1 - 1/Complex.abs z : ℝ)) * L.z₂ = (1 - 1/Complex.abs z : ℝ) * 0 + (1 - (1 - 1/Complex.abs z : ℝ)) * z := by exact rfl
        _= (1 - 1/Complex.abs z : ℝ) * 0 + (1 - (1 - 1/Complex.abs z : ℝ)) * z := by norm_num
        _= (1 - (1 - 1/Complex.abs z : ℝ)) * z := by ring
        _= (1 - (1 - 1/Complex.abs z )) * z := by simp
        _= z * (1/Complex.abs z) := by ring
        _= Complex.abs z * Complex.exp ((Complex.arg z : ℂ) * Complex.I) * (1/Complex.abs z) := by {
          simp
        }
        _= Complex.exp ((Complex.arg z : ℂ) * Complex.I) * (Complex.abs z / Complex.abs z) := by ring
        _= Complex.exp ((Complex.arg z : ℂ) * Complex.I) * 1 := by {
          aesop
        }
        _= Complex.exp ((Complex.arg z : ℂ) * Complex.I) := by simp

      · calc Complex.abs (Complex.exp ((Complex.arg z : ℂ) * Complex.I) - 0) = Complex.abs (Complex.exp ((Complex.arg z : ℂ) * Complex.I)) := by ring
        _= 1 := by {
          rw [Complex.abs_exp_ofReal_mul_I]
        }
        _= C.radius := by exact rfl
    }
    exact element_line_circle_intersection_constructible M h0 h1 L C hL hC (Complex.exp ((Complex.arg z : ℂ) * Complex.I )) hz'
}
-- no constructions needed anymore just combination of all the lemmas above
theorem constructible_numbers_closed_multiplication (M : Set ℂ) (h0: 0 ∈ M) (h1: 1 ∈M) (a b  : ℂ ) (ha : a ∈  constructible_numbers M (h0) (h1)) (hb : b ∈ constructible_numbers M (h0) (h1)) (ha' : a ≠0 ) (hb' : b ≠ 0):
a*b ∈ constructible_numbers M (h0) (h1) := by{
  have hab : a*b = Complex.abs a * Complex.exp ((Complex.arg a:ℂ) * Complex.I) * (Complex.abs b * Complex.exp ((Complex.arg b:ℂ) * Complex.I)) := by{
    simp
  }
  have hab' : Complex.exp ((Complex.arg a:ℂ) * Complex.I) * Complex.exp ((Complex.arg b:ℂ) * Complex.I)  = Complex.exp (((Complex.arg a:ℂ) +(Complex.arg b:ℂ)) * Complex.I) := by{
    rw [← Complex.exp_add]
    ring
  }
  have hab'' : a*b = Complex.abs a * Complex.abs b * Complex.exp (((Complex.arg a:ℂ) +(Complex.arg b:ℂ)) * Complex.I) := by{
    calc a*b = Complex.abs a * Complex.exp ((Complex.arg a:ℂ) * Complex.I) * (Complex.abs b * Complex.exp ((Complex.arg b:ℂ) * Complex.I)) := by exact hab
    _= Complex.abs a * Complex.abs b * (Complex.exp ((Complex.arg a:ℂ) * Complex.I) * Complex.exp ((Complex.arg b:ℂ) * Complex.I)) := by ring
    _= Complex.abs a * Complex.abs b * (Complex.exp (((Complex.arg a:ℂ) +(Complex.arg b:ℂ)) * Complex.I)) := by rw[hab']
  }
  have haabs: (Complex.abs a : ℂ)  ∈ constructible_numbers M (h0) (h1) := by{
    exact constructible_numbers_contains_abs M h0 h1 a ha
  }
  have hbabs: (Complex.abs b : ℂ)  ∈ constructible_numbers M (h0) (h1) := by{
    exact constructible_numbers_contains_abs M h0 h1 b hb
  }
  have haarg: Complex.exp ((Complex.arg a : ℂ) * Complex.I)  ∈ constructible_numbers M (h0) (h1) := by{
    exact constructible_numbers_contains_arg M h0 h1 a ha ha'
  }

  have haarg': Complex.exp ( Complex.I * (Complex.arg a : ℂ))  ∈ constructible_numbers M (h0) (h1) := by{
    rw [mul_comm]
    exact constructible_numbers_contains_arg M h0 h1 a ha ha'
  }

  have hbarg: Complex.exp ((Complex.arg b : ℂ) * Complex.I)  ∈ constructible_numbers M (h0) (h1) := by{
    exact constructible_numbers_contains_arg M h0 h1 b hb hb'
  }
  have hbarg': Complex.exp ( Complex.I * (Complex.arg b : ℂ))  ∈ constructible_numbers M (h0) (h1) := by{
    rw [mul_comm]
    exact constructible_numbers_contains_arg M h0 h1 b hb hb'
  }

  have hr : (Complex.abs a * Complex.abs b : ℂ)  ∈ constructible_numbers M (h0) (h1) := by{
    exact constructible_numbers_multiplication_pos_reals M h0 h1 (Complex.abs a) (Complex.abs b) (AbsoluteValue.pos Complex.abs ha') (AbsoluteValue.pos Complex.abs hb') haabs hbabs
  }
  have harg : Complex.exp (Complex.I * ((Complex.arg a:ℂ) +(Complex.arg b:ℂ)) )  ∈ constructible_numbers M (h0) (h1) := by{
    exact constructible_numbers_add_angles M h0 h1 (Complex.arg a) (Complex.arg b) haarg' hbarg'
  }
  have habs' : Complex.abs (a*b : ℂ ) = (Complex.abs a  * Complex.abs b  : ℂ)  := by{
    rw [@AbsoluteValue.map_mul]
    simp
  }

  have hφ : Complex.exp ((Complex.arg (a*b) : ℂ ) * Complex.I)  = Complex.exp (Complex.I * ((Complex.arg a:ℂ) +(Complex.arg b:ℂ)) ) := by{
        simp_rw [Complex.exp_eq_exp_iff_exists_int, ← mul_assoc _ (_*_), mul_comm _ Complex.I, ← mul_add,
        mul_eq_mul_left_iff, Complex.I_ne_zero, or_false, add_comm (_ + _), ← sub_eq_iff_eq_add,
        mul_comm _ (_*_)]
        norm_cast
        rw [← Real.Angle.angle_eq_iff_two_pi_dvd_sub, Real.Angle.coe_add, Complex.arg_mul_coe_angle ha' hb']
  }

  have hφ' : Complex.exp (Complex.arg (a*b) * Complex.I) ∈ constructible_numbers M (h0) (h1) := by{
    rw [hφ]
    exact harg
  }
  rw [← habs'] at hr
  exact construcible_numbers_contains_number_if_abs_and_arg M h0 h1 (a*b) (mul_ne_zero ha' hb')  hφ' hr
}
-- again main work for division is here, for the general case below we combine this lemma with others
lemma constructible_numbers_contains_reel_inverse (M: Set ℂ) (h0 : 0 ∈ M) (h1 : 1 ∈ M) (r : ℝ) (hr: (r : ℂ ) ∈ constructible_numbers M h0 h1) (hr' : r ≠ 0):
(r⁻¹ : ℂ ) ∈ constructible_numbers M h0 h1 := by{
  let r' : ℂ := ⟨r, 1⟩
  have hr'' : r' ∈ constructible_numbers M h0 h1 := by{
    let R : ℂ := ⟨r, 0⟩ + ⟨0, 1⟩
    have h : R ∈ constructible_numbers M (h0) (h1) := by{
      have hb'' : ⟨r,0⟩ + Complex.I  ∈ constructible_numbers M (h0) (h1) := by{
        exact constructible_numbers_closed_addition M h0 h1 ⟨r,0⟩ Complex.I (hr) (constructible_numbers_contains_I M h0 h1)
      }
      exact hb''
    }
    have h' : R = r' := by{
      refine Complex.ext_iff.mpr ?_
      constructor
      · simp
      · simp
    }
    exact Set.mem_of_eq_of_mem (id h'.symm) h
  }
  let L1 : line_through_two_points := {z₁ := 0, z₂ := r'}
  have hL1 : L1 ∈ constructible_lines (constructible_numbers M (h0) (h1)) := by{
    use 0
    use r'
    simp
    constructor
    · exact constructible_numbers_element_of M h0 h1 0 h0
    · exact hr''
  }
  let L2: line_through_two_points := {z₁ := 1, z₂ := 1 + Complex.I}
  have hL2 : L2 ∈ constructible_lines (constructible_numbers M (h0) (h1)) := by{
    use 1
    use 1 + Complex.I
    simp
    constructor
    · exact constructible_numbers_element_of M h0 h1 1 h1
    · exact constructible_numbers_closed_addition M h0 h1 1 Complex.I (constructible_numbers_element_of M h0 h1 1 h1) (constructible_numbers_contains_I M h0 h1)
  }

  have hll : L1.points ≠ L2.points := by{
    have hll₁ : 0 ∈ L1.points := by{
      exact line_through_two_points_beginn_in_points L1
    }
    have hll₂ : 0 ∉ L2.points := by{
      unfold line_through_two_points.points
      simp
      intro x
      ring
      intro hsmth
      apply_fun Complex.re at hsmth
      simp at hsmth
    }
    intro hsmth2
    rw[hsmth2] at hll₁
    exact hll₂ hll₁
  }

  have hrinv: ⟨1, r⁻¹⟩  ∈ L1.points ∩ L2.points := by{
    simp
    constructor
    · use (r - 1) / r
      calc ((r - 1) / r : ℝ ) * L1.z₁ + (1 - ((r - 1) / r : ℝ ) ) * L1.z₂ = ((r - 1) / r : ℝ ) * 0 + (1 - ((r - 1) / r : ℝ ) ) * r' := by exact rfl
      _= ((r - 1) / r : ℝ ) * 0 + (1 - ((r - 1) / r : ℝ ) ) * r' := by norm_num
      _= (1 - ((r - 1) / r : ℝ ) ) * r' := by ring
      _= (1 - ((r - 1) / r  ) ) * r' := by simp
      _= (1 - (r - 1) / r  ) * ⟨r,1⟩ := by simp
      _= (1 - (r / r - 1 / r )) * ⟨r,1⟩ := by ring
      _= (1 - (1 - 1 / r )) * ⟨r,1⟩ := by aesop
      _= (1 / r ) * ⟨r,1⟩ := by ring
      _= ⟨1 / r * r, 1 / r * 1⟩ := by {
        refine Complex.ext_iff.mpr ?_
        constructor
        · simp
        · simp
      }
      _= ⟨1, 1 / r * 1⟩ := by aesop
      _= ⟨1, 1 / r⟩ := by simp
      _= ⟨1, r⁻¹⟩ := by simp
    · use (r-1) / r
      calc ((r - 1) / r : ℝ ) * L2.z₁ + (1 - ((r - 1) / r : ℝ ) ) * L2.z₂ = ((r - 1) / r : ℝ ) * 1 + (1 - ((r - 1) / r : ℝ ) ) * (1 + Complex.I) := by exact rfl
      _= ((r - 1) / r : ℝ ) * 1 + (1 - ((r - 1) / r : ℝ ) ) * (1 + Complex.I) := by norm_num
      _= ((r - 1) / r ) + (1 - ((r - 1) / r  ) ) * (1 + Complex.I) := by simp
      _=  1  + (1 - ((r / r) - (1 / r))) * Complex.I := by ring
      _=  1  + (1 - (1 - (1 / r))) * Complex.I := by aesop
      _=  1  + ((1 / r)) * Complex.I := by ring
      _=  1  + ⟨0, (1 / r)⟩ := by {
        refine Complex.ext_iff.mpr ?_
        constructor
        · simp
        · simp
      }
      _= ⟨1, 1 / r⟩ := by {
        refine Complex.ext_iff.mpr ?_
        constructor
        · simp
        · simp
      }
      _= ⟨1, r⁻¹⟩ := by simp
  }
  have hrinv' : ⟨1, r⁻¹⟩  ∈ constructible_numbers M h0 h1 := by{
    exact element_line_line_intersection_constructible M h0 h1 L1 L2 hL1 hL2 ⟨1, r⁻¹⟩ hll hrinv
  }
  have hf: ⟨0, r⁻¹⟩ ∈ constructible_numbers M h0 h1 := by{
    exact constructible_numbers_contains_im M h0 h1 ⟨1, r⁻¹⟩ hrinv'
  }
  let C : circle_with_radius := {center := 0, radius := Complex.abs ⟨0,r⁻¹⟩}
  have hC : C ∈ constructible_circles (constructible_numbers M (h0) (h1)) := by{
    use 0
    use ⟨0,r⁻¹⟩
    use 0
    simp
    constructor
    · exact constructible_numbers_element_of M h0 h1 0 h0
    · constructor
      · exact hf
      · exact constructible_numbers_element_of M h0 h1 0 h0
  }
  let L : line_through_two_points := {z₁ := 0, z₂ := 1}
  have hL : L ∈ constructible_lines (constructible_numbers M (h0) (h1)) := by{
    use 0
    use 1
    simp
    constructor
    · exact constructible_numbers_element_of M h0 h1 0 h0
    · exact constructible_numbers_element_of M h0 h1 1 h1
  }
  have : ( r⁻¹ :ℂ ) ∈ L.points ∩ C.points := by{
    simp
    constructor
    · use 1 - r⁻¹
      calc (1 - r⁻¹ : ℝ ) * L.z₁ + (1 - (1 - r⁻¹ : ℝ ) ) * L.z₂ = (1 - r⁻¹ : ℝ ) * 0 + (1 - (1 - r⁻¹ : ℝ ) ) * 1 := by exact rfl
      _= (1 - r⁻¹ : ℝ ) * 0 + (1 - (1 - r⁻¹ : ℝ ) ) * 1 := by norm_num
      _= 0 + (1 - (1 - r⁻¹ : ℝ ) ) * 1 := by ring
      _= (1 + (- 1 + r⁻¹ )) * 1 := by simp
      _= r⁻¹ * 1 := by ring
      _= ⟨r⁻¹ * 1, r⁻¹ * 0⟩ := by {
        refine Complex.ext_iff.mpr ?_
        constructor
        · simp
        · simp
      }
      _= ⟨r⁻¹, 0⟩ := by simp
      _= (r⁻¹ :ℂ) := by {
        refine Complex.ext_iff.mpr ?_
        constructor
        · simp
        · simp
      }
    · calc Complex.abs ((r⁻¹ : ℂ ) - 0) = Complex.abs (⟨r⁻¹, 0⟩ -0 ) := by {
      have : (r⁻¹ : ℂ ) = ⟨r⁻¹, 0⟩  := by {
        refine Complex.ext_iff.mpr ?_
        constructor
        · simp
        · simp
      }
      rw [this]
    }
      _= Complex.abs ⟨r⁻¹, 0⟩ := by simp
      _= Real.sqrt ((r⁻¹)*(r⁻¹) + 0*0) := by exact rfl
      _= Real.sqrt (0*0 + (r⁻¹)*(r⁻¹)) := by ring
      _= Complex.abs ⟨0, r⁻¹⟩ := by exact rfl
      _= C.radius := by exact rfl
  }
  exact element_line_circle_intersection_constructible M h0 h1 L C hL hC (r⁻¹ : ℂ ) this

}

theorem constructible_numbers_contains_inverse (M :Set ℂ ) (h0 : 0 ∈ M) (h1 : 1 ∈ M) (a : ℂ ) (ha: a ∈ constructible_numbers M (h0) (h1)) (ha' : a ≠ 0):
a⁻¹ ∈ constructible_numbers M h0 h1 :=by{
  have ha'' : a = Complex.abs a * Complex.exp ((Complex.arg a:ℂ) * Complex.I) := by{
    simp
  }
  have ha''' : a⁻¹ = Complex.abs a⁻¹ * Complex.exp (- (Complex.arg (a) : ℂ)  * Complex.I) := by{
    rw[ha'']
    rw[@_root_.mul_inv_rev]
    simp
    have : (Complex.exp (↑(Complex.arg a) * Complex.I))⁻¹  = Complex.exp (- Complex.arg (a) * Complex.I) := by {
      rw [←Complex.exp_neg]
      simp
    }
    rw[this]
    ring
  }
  have ha'''' : conj (Complex.exp ((Complex.arg (a) ) * Complex.I)) = Complex.exp (-(Complex.arg (a) ) * Complex.I) := by{
    calc conj (Complex.exp ((Complex.arg (a) ) * Complex.I)) = Complex.exp (conj ((Complex.arg (a)) * Complex.I)) := by rw [← Complex.exp_conj]
    _= Complex.exp (conj ((Complex.arg (a) : ℂ)) * conj Complex.I) := by {
      have : conj (Complex.arg (a) * Complex.I) =  conj ((Complex.arg (a) : ℂ )) * conj Complex.I := by {
        calc conj (Complex.arg (a) * Complex.I) = conj ((Complex.arg (a) : ℂ )  * Complex.I)  := by simp
        _= conj ((Complex.arg (a) : ℂ )) * conj Complex.I := by simp
      }
      rw [this]
    }
    _= Complex.exp (conj ((Complex.arg (a) : ℂ )) * (- Complex.I)) := by rw[Complex.conj_I]
    _= Complex.exp (Complex.arg (a)  * (- Complex.I)) := by rw[Complex.conj_ofReal]
    _= Complex.exp (-(Complex.arg (a) ) * Complex.I) := by ring
  }
  rw[ha''']
  rw[← ha'''']
  have habs : (Complex.abs a⁻¹ : ℂ ) ∈ constructible_numbers M h0 h1 := by{
   have : (Complex.abs a⁻¹ : ℂ ) = (Complex.abs a)⁻¹ := by {
     rw [@map_inv₀]
   }
   rw [this]
   push_cast
   exact constructible_numbers_contains_reel_inverse M h0 h1 (Complex.abs a) (constructible_numbers_contains_abs M h0 h1 a ha) (AbsoluteValue.ne_zero Complex.abs ha')
  }
  have harg : conj (Complex.exp ((Complex.arg (a)) * Complex.I)) ∈ constructible_numbers M h0 h1 := by{
    have : Complex.exp ((Complex.arg (a)) * Complex.I) ∈ constructible_numbers M h0 h1 := by{
      exact constructible_numbers_contains_arg M h0 h1 a ha ha'
    }
    exact constructible_numbers_closed_complex_conjugation M h0 h1 (Complex.exp ((Complex.arg a : ℂ ) * Complex.I)) this
  }
  have habsnotnull : (Complex.abs a⁻¹ : ℂ ) ≠ 0 := by{
    simp
    push_neg
    exact ha'
  }
  have hargnotnull : (conj (Complex.exp ((Complex.arg (a)) * Complex.I))) ≠ 0 := by{
    have : Complex.exp (-(Complex.arg (a)) * Complex.I) ≠ 0 := by{
      exact Complex.exp_ne_zero (-(Complex.arg a : ℂ ) * Complex.I)
    }
    exact Eq.trans_ne ha'''' this
  }

  exact constructible_numbers_closed_multiplication M h0 h1 (Complex.abs a⁻¹) (conj (Complex.exp ((Complex.arg (a)) * Complex.I))) habs harg (habsnotnull) (hargnotnull)
}
-- again main work for real square roots is here, for the general case below we combine this lemma with others
lemma constructible_numbers_contains_reel_sq_gt_1 (M : Set ℂ) (h0 : 0 ∈ M) (h1 : 1 ∈ M) (r : ℝ) (h: r ≥ 1) (hr: (r : ℂ ) ∈ constructible_numbers M h0 h1) : (Real.sqrt r : ℂ ) ∈ constructible_numbers M h0 h1 := by{
  have hr' : (r/2 : ℂ)  ∈ constructible_numbers M h0 h1 := by{
    have : (r / 2 :ℂ ) = (0 + r) /2 := by simp
    rw [this]
    exact constructible_numbers_half_point M h0 h1 0 r (constructible_numbers_element_of M h0 h1 0 h0) hr
  }
  let C : circle_with_radius := {center := (r / 2 : ℂ ), radius := Complex.abs (⟨r/2, 0⟩)}
  have hC : C ∈ constructible_circles (constructible_numbers M h0 h1) := by{
    use ⟨r/2,0⟩
    use r/2
    use 0
    simp
    have : (r / 2 :ℂ ) = ⟨r/2, 0⟩ := by {
      refine Complex.ext_iff.mpr ?_
      constructor
      · simp
      · simp
    }
    rw[←this]
    constructor
    · simp
    · constructor
      · exact hr'
      · constructor
        · exact hr'
        · exact constructible_numbers_element_of M h0 h1 0 h0
  }
  let L : line_through_two_points := {z₁ := 1, z₂ := 1 + Complex.I}
  have hL : L ∈ constructible_lines (constructible_numbers M h0 h1) := by{
    use 1
    use 1 + Complex.I
    simp
    constructor
    · exact constructible_numbers_element_of M h0 h1 1 h1
    · exact constructible_numbers_closed_addition M h0 h1 1 Complex.I (constructible_numbers_element_of M h0 h1 1 h1) (constructible_numbers_contains_I M h0 h1)
  }

  let z : ℂ := ⟨1, Real.sqrt (r-1)⟩
  have hz : z ∈ L.points ∩ C.points:= by{
    simp
    constructor
    · use 1 - Real.sqrt (r-1)
      calc (1 - Real.sqrt (r-1) : ℝ ) * L.z₁ + (1 - (1 - Real.sqrt (r-1) : ℝ ) ) * L.z₂ = (1 - Real.sqrt (r-1) : ℝ ) * 1 + (1 - (1 - Real.sqrt (r-1) : ℝ ) ) * (1 + Complex.I) := by exact rfl
      _= (1 - Real.sqrt (r-1) : ℝ ) * 1 + (1 - (1 - Real.sqrt (r-1) : ℝ ) ) * (1 + Complex.I) := by norm_num
      _= (1 - Real.sqrt (r-1)) * 1 + (1 - (1 - Real.sqrt (r-1)) ) * (1 + Complex.I) :=  by simp
      _= 1 + Real.sqrt (r-1) * Complex.I  := by ring
      _= ⟨1, Real.sqrt (r-1)⟩ := by {
        refine Complex.ext_iff.mpr ?_
        constructor
        · simp
        · simp
      }
    · calc Complex.abs (z - (r / 2 : ℂ )) = Complex.abs (⟨1, Real.sqrt (r-1)⟩ - (r / 2 : ℂ )) := by exact rfl
      _= Complex.abs (⟨1, Real.sqrt (r-1)⟩ - ⟨r/2, 0⟩) := by {
        have : (r / 2 :ℂ ) = ⟨r/2, 0⟩ := by {
          refine Complex.ext_iff.mpr ?_
          constructor
          · simp
          · simp
        }
        rw [this]
      }
      _= Complex.abs (⟨1 - r/2, Real.sqrt (r-1) -0⟩) := by exact rfl
      _= Complex.abs (⟨1 - r/2, Real.sqrt (r-1)⟩) := by simp
      _= Real.sqrt ((1 - r/2)*(1 - r/2) + (Real.sqrt (r-1))*(Real.sqrt (r-1))) := by exact rfl
      _= Real.sqrt ((1 - r/2)*(1 - r/2) + (r-1)) := by {
        have : (Real.sqrt (r-1))*(Real.sqrt (r-1)) = (r-1) := by {
          have : (r -1) ≥ 0 := by linarith
          exact Real.mul_self_sqrt this
        }
        rw [this]
      }
      _= Real.sqrt ((r/2) * (r/2) + 0*0) := by ring
      _= Complex.abs (⟨r/2, 0⟩) := by exact rfl
      _= C.radius := by exact rfl
  }
  have hz' : z ∈ constructible_numbers M h0 h1 := by{
    exact element_line_circle_intersection_constructible M h0 h1 L C hL hC z hz
  }
  let C2 : circle_with_radius := {center := 0, radius := Complex.abs z}
  let L2 : line_through_two_points := {z₁ := 0, z₂ := 1}
  have hC2 : C2 ∈ constructible_circles (constructible_numbers M h0 h1) := by{
    use 0
    use Complex.abs z
    use 0
    simp
    constructor
    · exact constructible_numbers_element_of M h0 h1 0 h0
    · constructor
      · exact constructible_numbers_contains_abs M h0 h1 z hz'
      · exact constructible_numbers_element_of M h0 h1 0 h0
  }
  have hL2 : L2 ∈ constructible_lines (constructible_numbers M h0 h1) := by{
    use 0
    use 1
    simp
    constructor
    · exact constructible_numbers_element_of M h0 h1 0 h0
    · exact constructible_numbers_element_of M h0 h1 1 h1
  }
  have : (Real.sqrt r : ℂ ) ∈  L2.points ∩ C2.points := by {
    constructor
    · use 1 - Real.sqrt r
      calc (1 - Real.sqrt r : ℝ ) * L2.z₁ + (1 - (1 - Real.sqrt r : ℝ ) ) * L2.z₂ = (1 - Real.sqrt r : ℝ ) * 0 + (1 - (1 - Real.sqrt r : ℝ ) ) * 1 := by exact rfl
      _= (1 - Real.sqrt r ) * 0 + (1 - (1 - Real.sqrt r ) ) * 1 := by simp
      _= Real.sqrt r := by ring
    · calc Complex.abs ((Real.sqrt r : ℂ ) - 0) = Complex.abs ((Real.sqrt r): ℂ  ) := by ring
      _= Complex.abs (⟨Real.sqrt r, 0⟩) := by {
        have : (Real.sqrt r :ℂ ) = ⟨Real.sqrt r, 0⟩ := by {
          refine Complex.ext_iff.mpr ?_
          constructor
          · simp
          · simp
        }
        rw [this]
      }
      _= Real.sqrt ((Real.sqrt r)*(Real.sqrt r) + 0*0) := by exact rfl
      _= Real.sqrt (r) := by {
        have : (Real.sqrt r)*(Real.sqrt r) = r := by {
          have : r ≥ 0 := by linarith
          exact Real.mul_self_sqrt this
        }
        rw [this]
        simp
      }
      _= Real.sqrt (r - 1 +1) := by ring
      _= Real.sqrt (1 * 1 + Real.sqrt (r-1) * Real.sqrt (r-1)) := by{
        have : (Real.sqrt (r-1))*(Real.sqrt (r-1)) = (r-1) := by {
          have : (r -1) ≥ 0 := by linarith
          exact Real.mul_self_sqrt this
        }
        rw [this]
        ring
      }
      _= Complex.abs (⟨1, Real.sqrt (r-1)⟩) := by exact rfl
  }
  exact element_line_circle_intersection_constructible M h0 h1 L2 C2 hL2 hC2 (Real.sqrt r : ℂ ) this
}

lemma constructible_numbers_contains_reel_sq (M : Set ℂ) (h0 : 0 ∈ M) (h1 : 1 ∈ M) (r : ℝ) (h: r > 0) (hr: (r : ℂ ) ∈ constructible_numbers M h0 h1) : (Real.sqrt r : ℂ ) ∈ constructible_numbers M h0 h1 := by{
  by_cases h' : r ≥ 1
  · exact constructible_numbers_contains_reel_sq_gt_1 M h0 h1 r h' hr
  · have hr1 : 1/r ≥ 1 := by{
      refine (le_div_iff h).mpr ?_
      linarith
    }
    have hr2 : ((1 / r): ℂ)  ∈ constructible_numbers M h0 h1 := by{
      have : r ≠ 0 := by linarith
      have t : (r : ℂ) ≠ 0 := by norm_cast
      have : (r: ℂ )⁻¹ = (1 / (r : ℂ)) := by {
        rw [inv_eq_one_div]
      }
      rw[← this]
      exact constructible_numbers_contains_inverse M h0 h1 (r : ℂ ) hr t
    }
    have : (1 / (r : ℂ )) = ↑(1/r):= by simp
    rw[this] at hr2
    have hr3 : (Real.sqrt (1/r) : ℂ ) ∈ constructible_numbers M h0 h1 := by{

      exact constructible_numbers_contains_reel_sq_gt_1 M h0 h1 (1/r) hr1 hr2
    }
    have hr4 :  ((Real.sqrt (1/r)) : ℂ )⁻¹ ∈ constructible_numbers M h0 h1 := by{
      have hr4' : Real.sqrt (1 / r) ≠ 0 := by {
        simp
        exact h
      }
      have : (↑(Real.sqrt (1 / r)))⁻¹ = (1 / (Real.sqrt (1 / r) : ℂ )) := by {
        rw [inv_eq_one_div]
      }

      exact constructible_numbers_contains_reel_inverse M h0 h1 (Real.sqrt (1/r) ) hr3 hr4'
      }
    have : ((Real.sqrt (1/r)) : ℂ )⁻¹ = (Real.sqrt (r) : ℂ ) := by simp
    rw[← this]
    exact hr4
}

--Lean somehow couldn't apply the following 3 lemma from the mathlib, but did it if i use these ones
lemma double_angle_sin (a : ℝ ) : Real.sin (a + a) = 2 * Real.sin a * Real.cos a := by{
  rw [Real.sin_add]
  ring
}
lemma double_angle_cos (a : ℝ ) : Real.cos (a + a) = Real.cos a * Real.cos a - Real.sin a * Real.sin a := by{
  rw [Real.cos_add]
}
lemma power (a : ℂ ) : a^2 = a * a := by {
  ring
}

lemma constructible_numbers_half_angle (M :Set ℂ ) (h0 : 0 ∈ M) (h1 : 1 ∈ M) (a : ℝ) (hh1 : a ≤  Real.pi) (hh2 : a > -Real.pi) (ha: Complex.exp (a * Complex.I) ∈ constructible_numbers M (h0) (h1)) :
 Complex.exp ( a/2 * Complex.I) ∈ constructible_numbers M h0 h1 := by{
  by_cases h : a = 0
  · rw [h]
    simp
    exact constructible_numbers_element_of M h0 h1 1 h1
  · by_cases h' : a = Real.pi
    · rw [h']
      have : Complex.exp (Real.pi / 2 * Complex.I) = Complex.I := by {
        calc Complex.exp (Real.pi / 2 * Complex.I) = Complex.cos (Real.pi / 2) + Complex.sin (Real.pi / 2) * Complex.I := by exact Complex.exp_mul_I (Real.pi / 2 : ℂ )
        _= 0 + 1 * Complex.I := by simp
        _= Complex.I := by ring
      }
      rw [this]
      exact constructible_numbers_contains_I M h0 h1
    · let C  : circle_with_radius := {center := 0, radius := Complex.abs 1}
      have hC : C ∈ constructible_circles (constructible_numbers M h0 h1) := by{
        use 0
        use 1
        use 0
        simp
        constructor
        · exact constructible_numbers_element_of M h0 h1 0 h0
        · constructor
          · exact constructible_numbers_element_of M h0 h1 1 h1
          · exact constructible_numbers_element_of M h0 h1 0 h0
      }
      have hhalf: (1 + Complex.exp ( a * Complex.I)) / 2 ∈ constructible_numbers M h0 h1 := by{
        exact constructible_numbers_half_point M h0 h1 1 (Complex.exp (a * Complex.I)) (constructible_numbers_element_of M h0 h1 1 h1) ha
      }
      let L : line_through_two_points := {z₁ := 0, z₂ := (1 + Complex.exp (a * Complex.I)) /2}
      have hL : L ∈ constructible_lines (constructible_numbers M h0 h1) := by{
        use 0
        use (1 + Complex.exp (a * Complex.I)) /2
        simp
        constructor
        · exact constructible_numbers_element_of M h0 h1 0 h0
        · exact hhalf
      }
      have : Complex.exp (a/2 * Complex.I) ∈ L.points ∩ C.points := by{
        constructor
        · use 1 - 2 * Real.sin (a/2) * 1/ Real.sin (a)
          calc (1 - 2 * Real.sin (a/2) * 1/ Real.sin (a) : ℝ ) * L.z₁ + (1 - (1 - 2 * Real.sin (a/2) * 1/ Real.sin (a) : ℝ ) ) * L.z₂ = (1 - 2 * Real.sin (a/2) * 1/ Real.sin (a) : ℝ ) * 0 + (1 - (1 - 2 * Real.sin (a/2) * 1/ Real.sin (a) : ℝ ) ) * ((1 + Complex.exp (a * Complex.I)) /2) := by exact rfl
          _=  ( 2 * Real.sin (a/2) * 1/ Real.sin (a) )  * ((1 + Complex.exp (a * Complex.I)) /2) := by norm_num
          _= ((  Real.sin (a/2) * 1/ Real.sin (a/2 + a/2) ) + (  Real.sin (a/2) * 1/ Real.sin (a/2 + a/2) ) * Complex.exp (a * Complex.I)) := by ring
          _= ((  Real.sin (a/2) * 1/ Real.sin (a/2 + a/2) ) + (  Real.sin (a/2) * 1/ Real.sin (a/2 + a/2) ) * (Real.cos (a/2 + a/2) + Real.sin (a / 2 + a/2) * Complex.I)) := by aesop
          _= ((  Real.sin (a/2) * 1/ (2*Real.sin (a/2)*Real.cos (a/2))) + (  Real.sin (a/2) * 1/ (2 * Real.sin (a/2) *Real.cos (a/2)) ) * ((Real.cos (a/2) * Real.cos (a/2) - Real.sin (a/2) * Real.sin (a/2)) + (2*Real.sin (a/2) * Real.cos (a/2))* Complex.I)) := by{
            rw [double_angle_sin]
            rw [Real.cos_add]
            simp
          }
          _= ((1/2 * (Real.sin (a/2) / Real.sin (a/2)) * 1/Real.cos (a/2)) + 1/2 * (Real.sin (a/2) / Real.sin (a/2)) * 1/ Real.cos (a/2) * ((Real.cos (a/2) * Real.cos (a/2) - Real.sin (a/2) * Real.sin (a/2)) + (2*Real.sin (a/2) * Real.cos (a/2))* Complex.I)) := by ring
          _= ((1/2 * (Real.sin (a/2) / Real.sin (a/2) : ℝ ) * 1/Real.cos (a/2)) + 1/2 * (Real.sin (a/2) / Real.sin (a/2) : ℝ ) * 1/ Real.cos (a/2) * ((Real.cos (a/2) * Real.cos (a/2) - Real.sin (a/2) * Real.sin (a/2)) + (2*Real.sin (a/2) * Real.cos (a/2))* Complex.I)) := by simp
          _= ((1/2  *  1/Real.cos (a/2)) + 1/2 * 1/ Real.cos (a/2) * ((Real.cos (a/2) * Real.cos (a/2) - Real.sin (a/2) * Real.sin (a/2)) + (2*Real.sin (a/2) * Real.cos (a/2))* Complex.I)) := by{
            have : Real.sin (a/2) / Real.sin (a/2)  = 1 := by{
              by_cases ht : a < 0
              · have t0 : a/2 < 0 := by linarith
                have t1 : a/2 > - Real.pi /2 := by linarith
                have t3 : Real.sin (a/2) < 0 := by {
                  exact Real.sin_neg_of_neg_of_neg_pi_lt t0 (by linarith)
                }
                have t4 : Real.sin (a/2) ≠ 0 := by linarith
                exact div_self t4
              · push_neg at ht
                have : a > 0 := by exact Ne.lt_of_le' h ht
                have t0 : a /2 > 0 := by linarith
                have : a < Real.pi := by exact Ne.lt_of_le h' hh1
                have t1 : a/2 < Real.pi := by linarith
                have t3 : Real.sin (a/2) > 0 := by {
                  exact Real.sin_pos_of_pos_of_lt_pi t0 t1
                }
                have t4 : Real.sin (a/2) ≠ 0 := by linarith
                exact div_self t4
            }
            rw [this]
            simp
          }
          _= 1/2* 1/ Real.cos (a/2) + 1/2*1/Real.cos (a/2) * (Real.cos (a/2)* Real.cos (a/2) - Real.sin (a/2)* Real.sin (a/2)) + 1/2 * (Real.cos (a/2) / Real.cos (a/2)) * (2*Real.sin (a/2))* Complex.I := by ring
          _= 1/2* 1/ Real.cos (a/2) + 1/2*1/Real.cos (a/2) * (Real.cos (a/2)* Real.cos (a/2) - Real.sin (a/2)* Real.sin (a/2)) + 1/2 * (Real.cos (a/2) / Real.cos (a/2) : ℝ ) * (2*Real.sin (a/2))* Complex.I := by simp
          _= 1/2* 1/ Real.cos (a/2) + 1/2*1/Real.cos (a/2) * (Real.cos (a/2)* Real.cos (a/2) - Real.sin (a/2)* Real.sin (a/2)) + Real.sin (a/2)* Complex.I := by {
            have : Real.cos (a/2) / Real.cos (a/2) = 1 := by {
              by_cases ht : a ≤ Real.pi
              · have t0 : a < Real.pi := by exact Ne.lt_of_le h' ht
                have t1 : a/2 < Real.pi /2 := by linarith
                have t2 : a/2 > - Real.pi /2 := by linarith
                have t3 : a/2 ∈ Set.Ioo (- (Real.pi /2)) (Real.pi /2) := by {
                  simp
                  constructor
                  · linarith
                  · linarith
                }
                have t4 : Real.cos (a/2) > 0 := by {
                  exact Real.cos_pos_of_mem_Ioo t3
                }
                exact div_self (ne_of_gt t4)
              · push_neg at ht
                have t0 : a/2 > Real.pi /2 := by linarith
                have t1 : a/2 < Real.pi + Real.pi /2 := by linarith
                have t3 : Real.cos (a/2) < 0 := by {
                  exact Real.cos_neg_of_pi_div_two_lt_of_lt t0 t1
                }
                have t4 : Real.cos (a/2) ≠ 0 := by linarith
                exact div_self t4
            }
            rw [this]
            simp
          }
          _= (1+ Real.cos (a/2) * Real.cos (a/2) - Real.sin (a/2) * Real.sin (a/2)) / (2 * Real.cos (a/2)) + Real.sin (a/2)* Complex.I := by ring
          _= (1 + Real.cos (a/2) * Real.cos (a/2) - Real.sin (a/2) * Real.sin (a/2) + (1) - (1)) / (2 * Real.cos (a/2)) + Real.sin (a/2)* Complex.I := by norm_num
          _= (1 + Real.cos (a/2) * Real.cos (a/2) - Real.sin (a/2) * Real.sin (a/2) + ((Real.sin (a/2) ^ 2) + (Real.cos (a/2) ^ 2)) - 1) / (2 * Real.cos (a/2)) + Real.sin (a/2)* Complex.I := by{
             simp [Real.sin_sq_add_cos_sq (a/2)]
            }
          _= (1 + Real.cos (a/2) * Real.cos (a/2) - Real.sin (a/2) * Real.sin (a/2) + ((Real.sin (a/2) * Real.sin (a/2)) + (Real.cos (a/2) * Real.cos (a/2))) - 1) / (2 * Real.cos (a/2)) + Real.sin (a/2)* Complex.I := by{
              simp [power]
            }
          _=  Real.cos (a/2) * (Real.cos (a/2) / Real.cos (a/2)) + Real.sin (a/2) * Complex.I := by ring
          _= Real.cos (a/2) * (Real.cos (a/2) / Real.cos (a/2) : ℝ) + Real.sin (a/2) * Complex.I := by simp
          _= Real.cos (a/2) + Real.sin (a/2) * Complex.I := by{
             have : Real.cos (a/2) / Real.cos (a/2) = 1 := by {
              by_cases ht : a ≤ Real.pi
              · have t0 : a < Real.pi := by exact Ne.lt_of_le h' ht
                have t1 : a/2 < Real.pi /2 := by linarith
                have t2 : a/2 > - Real.pi /2 := by linarith
                have t3 : a/2 ∈ Set.Ioo (- (Real.pi /2)) (Real.pi /2) := by {
                  simp
                  constructor
                  · linarith
                  · linarith
                }
                have t4 : Real.cos (a/2) > 0 := by {
                  exact Real.cos_pos_of_mem_Ioo t3
                }
                exact div_self (ne_of_gt t4)
              · push_neg at ht
                have t0 : a/2 > Real.pi /2 := by linarith
                have t1 : a/2 < Real.pi + Real.pi /2 := by linarith
                have t3 : Real.cos (a/2) < 0 := by {
                  exact Real.cos_neg_of_pi_div_two_lt_of_lt t0 t1
                }
                have t4 : Real.cos (a/2) ≠ 0 := by linarith
                exact div_self t4
            }
             rw [this]
             simp
          }
          _= Complex.cos (a/2) + Complex.sin (a/2) * Complex.I := by aesop
          _= Complex.exp (a/2 * Complex.I) := by rw [Complex.cos_add_sin_I]
        · calc Complex.abs (Complex.exp (a/2 * Complex.I) - 0) = Complex.abs (Complex.exp ((a/2) * Complex.I)) := by simp
          _= Complex.abs (Complex.exp (a/2 * Complex.I)) := by ring
          _= 1 := by{
            rw [Complex.abs_eq_one_iff]
            use a/2
            simp
          }
          _= Complex.abs 1 := by simp
          _= C.radius := by exact rfl
      }
      exact element_line_circle_intersection_constructible M h0 h1 L C hL hC (Complex.exp (a/2 * Complex.I)) this
}
-- complex square roots arent defined in mathlib so i formulated it in the way that there exists a number s.th. its square is the given number
lemma constructible_numbers_contain_complex_root (M : Set ℂ) (h0 : 0 ∈ M) (h1 : 1 ∈ M) (z : ℂ) (hz : z ∈ constructible_numbers M h0 h1) :
  ∃ z' ∈ constructible_numbers M h0 h1, z' * z' = z := by{
    let z' : ℂ := Real.sqrt (Complex.abs z) * Complex.exp (Complex.arg z / 2 * Complex.I)
    have hz' : z' * z' = z := by{
      calc z' * z' = (Real.sqrt (Complex.abs z) * Complex.exp (Complex.arg z / 2 * Complex.I)) * (Real.sqrt (Complex.abs z) * Complex.exp (Complex.arg z / 2 * Complex.I)) := by exact rfl
      _= Real.sqrt (Complex.abs z) * Real.sqrt (Complex.abs z) * Complex.exp (Complex.arg z / 2 * Complex.I) * Complex.exp (Complex.arg z / 2 * Complex.I) := by ring
      _= ((Real.sqrt (Complex.abs z) ) * (Real.sqrt (Complex.abs z) ) : ℝ )   * Complex.exp (Complex.arg z / 2 * Complex.I) * Complex.exp (Complex.arg z / 2 * Complex.I) := by norm_cast
      _= Complex.abs z * Complex.exp (Complex.arg z / 2 * Complex.I) * Complex.exp (Complex.arg z / 2 * Complex.I) := by {
        have t0: Real.sqrt (Complex.abs z) * Real.sqrt (Complex.abs z) = Complex.abs z := by {
          have : Complex.abs z ≥ 0 := by simp
          exact Real.mul_self_sqrt this
        }
        simp [t0]
      }
      _= Complex.abs z * (Complex.exp (Complex.arg z / 2 * Complex.I) * Complex.exp (Complex.arg z / 2 * Complex.I)) := by ring
      _= Complex.abs z * Complex.exp (Complex.arg z / 2 * Complex.I + Complex.arg z / 2 * Complex.I) := by rw [Complex.exp_add]
      _= Complex.abs z * Complex.exp (Complex.arg z * Complex.I) := by ring
      _= z := by simp
    }
    use z'
    by_cases h : Complex.abs (z) = 0
    · have hzn : z= 0 := by {
          have : z = Complex.abs z * Complex.exp (Complex.arg z * Complex.I) := by {
            simp
          }
          rw [this]
          simp [h]
      }
      have : z' = 0 := by {
        simp
        left
        exact hzn
      }
      simp [this]
      constructor
      · exact constructible_numbers_element_of M h0 h1 0 h0
      · exact id hzn.symm
    · have hr : (Real.sqrt (Complex.abs (z)) : ℂ) ∈ constructible_numbers M h0 h1 := by{
        have : Complex.abs (z) > 0 := by {
          simp
          exact ne_zero_of_map h
        }
        have hr' : (Complex.abs (z):ℂ ) ∈ constructible_numbers M h0 h1 := by {
          exact constructible_numbers_contains_abs M h0 h1 z hz
        }
        exact constructible_numbers_contains_reel_sq M h0 h1 (Complex.abs (z)) (this) hr'
      }
      have harg : Complex.exp (Complex.arg z /2 * Complex.I) ∈ constructible_numbers M h0 h1 := by{
        have harg': Complex.arg (z) ∈ Set.Ioc (-Real.pi) Real.pi  := by {
          exact Complex.arg_mem_Ioc (z)
        }
        exact constructible_numbers_half_angle M h0 h1 (Complex.arg (z)) harg'.right harg'.left (constructible_numbers_contains_arg M h0 h1 z hz (ne_zero_of_map h))
      }
      have hr' : (Real.sqrt (Complex.abs (z)) : ℂ) ≠ 0 := by {
        simp
        exact ne_zero_of_map h
      }
      constructor
      · exact constructible_numbers_closed_multiplication M h0 h1 (Real.sqrt (Complex.abs (z))) (Complex.exp (Complex.arg (z) / 2 * Complex.I)) hr harg (hr') (Complex.exp_ne_zero (Complex.arg (z) / 2 * Complex.I))
      · exact hz'
}

-- i used {0,1} for the subfield structure, but as all the lemma are more general we can substitute {0,1} wit any set M s.th. 0,1 ∈ M and get a subfield
-- but not nesesarily the smallest one closed under taking squareroots
-- For example can be used to prove that trisecting an arbitrary angle is not possible with a compass and straightedge, by using the set {0, 1, e^{i*angle} instead of {0,1}
def constructibleNumberSubfield : Subfield ℂ :=
{ carrier := constructible_numbers ({(0 : ℂ ),(1 : ℂ )}) (by simp) (by simp)
  mul_mem' := by{
    intro a b ha hb
    by_cases ha' : a = 0
    · rw [ha']
      simp
      exact Set.mem_of_eq_of_mem (id ha'.symm) ha
    · by_cases hb' : b = 0
      · rw [hb']
        simp
        exact Set.mem_of_eq_of_mem (id hb'.symm) hb
      · exact constructible_numbers_closed_multiplication ({(0 : ℂ ),(1 : ℂ )}) (by simp) (by simp) a b ha hb ha' hb'
  }
  one_mem' := by{
    exact constructible_numbers_element_of ({(0 : ℂ ),(1 : ℂ )}) (by simp) (by simp) 1 (by simp)
  }
  zero_mem' := by{
    exact constructible_numbers_element_of ({(0 : ℂ ),(1 : ℂ )}) (by simp) (by simp) 0 (by simp)
  }
  add_mem' := by{
    intro a b ha hb
    exact constructible_numbers_closed_addition ({(0 : ℂ ),(1 : ℂ )}) (by simp) (by simp) a b ha hb
  }
  neg_mem' := by{
    intro a ha
    exact constructible_numbers_additive_inverse ({(0 : ℂ ),(1 : ℂ )}) (by simp) (by simp) a ha
  }
  inv_mem' := by{
    intro a ha
    by_cases ha' : a = 0
    · rw [ha']
      simp
      exact Set.mem_of_eq_of_mem (id ha'.symm) ha
    · exact constructible_numbers_contains_inverse ({(0 : ℂ ),(1 : ℂ )}) (by simp) (by simp) a ha ha'
  }
}
