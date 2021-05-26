import Lean

structure GameState where
  position : Nat
  goal : Nat

def allowed_move : GameState → GameState → Prop
| ⟨n, g⟩, ⟨m, h⟩ => (m + 1 = n ∧ g = h) ∨ (m = n + 1 ∧ g = h)

def is_win : GameState → Prop
| ⟨n, m⟩ => n = m

def can_win (g : GameState) : Prop :=
  ∃ (n : Nat),
  ∃ (m : Nat → GameState),
  (g = m n) ∧
  (is_win (m 0)) ∧
  (∀ (i : Nat), i < n → allowed_move (m i) (m (i + 1)))

theorem step_left {g : GameState} (h : can_win g) : can_win ⟨g.position + 1, g.goal⟩ :=
  ⟨h.1 + 1,
   by admit⟩
