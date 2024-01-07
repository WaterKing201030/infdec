import Infdec.Digits.Base

/-
Things needed related to orders
- eq √
  - refl √
  - symm √
  - trans √
- ne √
  - irrefl √
  - symm √
- le √
  - refl √
  - antisymm √
  - trans √
- lt √
  - irrefl √
  - asymm √
  - trans √
- relations
  - ne.intro √
  - ne.elim √
  - ne_iff_not_eq √
  - eq.to_le √
  - lt.to_le √
  - le_iff_eq_or_lt √
  - eq_or_lt_of_le √
  - lt.to_ne √
  - lt_of_le_of_ne √
  - lt_iff_le_and_ne √
- decidable √
- total
  - eq_or_ne √
  - lt_of_not_ge √
  - le_of_not_gt √
  - not_lt_of_ge √
  - not_le_of_gt √
  - lt_iff_not_ge √
  - le_iff_not_gt √
  - le.total √
  - le_or_gt √
  - lt_or_gt_of_ne √
  - trichotomous √
- trans
  - ne_of_eq_of_ne √
  - ne_of_ne_of_eq √
  - le_of_eq_of_le √
  - le_of_le_of_eq √
  - lt_of_eq_of_lt √
  - lt_of_lt_of_eq √
  - lt_of_le_of_lt √
  - lt_of_lt_of_le √
- zero
  - (optional) zero_unique
  - zero_le
  - not_lt_zero
-/

namespace wkmath

namespace Digits

namespace len
section define
def eq:Digits → Digits → Prop
  | ε, ε => True
  | ε, _::_
  | _::_, ε => False
  | a::_, b::_ => eq a b

notation:50 lhs:51 " =L " rhs:51 => len.eq lhs rhs

def ne:Digits → Digits → Prop
  | ε, ε => False
  | ε, _::_
  | _::_, ε => True
  | a::_, b::_ => ne a b

notation:50 lhs:51 " ≠L " rhs:51 => len.ne lhs rhs

def le:Digits → Digits → Prop
  | ε, ε
  | ε, _::_ => True
  | _::_, ε => False
  | a::_, b::_ => le a b

notation:50 lhs:51 " ≤L " rhs:51 => len.le lhs rhs

def lt:Digits → Digits → Prop
  | ε, ε
  | _::_, ε => False
  | ε, _::_ => True
  | a::_, b::_ => lt a b

notation: 50 lhs:51 " <L " rhs:51 => len.lt lhs rhs
end define
section property
theorem eq.refl(x:Digits):x =L x:=by{
  induction x with
  | nil => simp[eq]
  | cons _ _ ih => rw[eq] at *; exact ih
}

theorem eq.symm{x y:Digits}(h:x =L y):y =L x:=by{
  match x, y with
  | ε, ε => exact refl _
  | _::_, _::_ => rw[eq] at *; exact h.symm
}

theorem eq.trans{x y z:Digits}(h0:x =L y)(h1:y =L z):x =L z:=by{
  match x, y, z with
  | ε, _::_, _
  | _::_, ε, _
  | _, ε, _::_
  | _, _::_, ε => contradiction
  | ε, _, ε => exact refl _
  | _::_, _::_, _::_ => rw[eq] at *; exact h0.trans h1
}

theorem ne.irrefl(x:Digits):¬x ≠L x:=by{
  induction x with
  | nil => simp[ne]
  | cons _ _ ih => rw[ne] at *; exact ih
}

theorem ne.symm{x y:Digits}(h:x ≠L y):y ≠L x:=by{
  match x, y with
  | cons _ _, ε
  | ε, cons _ _ => simp[ne]
  | cons _ _, cons _ _ => rw[ne] at *; exact h.symm
}

theorem le.refl(x:Digits):x ≤L x:=by{
  induction x with
  | nil => simp[le]
  | cons _ _ ih => rw[le]; exact ih
}

theorem le.antisymm{x y:Digits}(h0:x ≤L y)(h1:y ≤L x):x =L y:=by{
  match x, y with
  | ε, ε => simp[eq]
  | cons _ _, cons _ _ => rw[le] at *; rw[eq]; exact antisymm h0 h1
}

theorem le.trans{x y z:Digits}(h0:x ≤L y)(h1:y ≤L z):x ≤L z:=by{
  match x, y, z with
  | _::_, ε, _
  | _, _::_, ε => contradiction
  | ε, _, ε
  | ε, _, cons _ _ => simp[le]
  | _::_, _::_, _::_ => rw[le] at *; exact h0.trans h1
}

theorem lt.irrefl(x:Digits):¬x <L x:=by{
  induction x with
  | nil => simp[lt]
  | cons _ _ ih => rw[lt]; exact ih
}

theorem lt.asymm{x y:Digits}(h:x <L y):¬y <L x:=by{
  match x, y with
  | ε, _::_ => simp[lt]
  | _::_, _::_ => rw[lt] at *; exact h.asymm
}

theorem lt.trans{x y z:Digits}(h0:x <L y)(h1:y <L z):x <L z:=by{
  match x, y, z with
  | _::_, ε, _
  | _, ε, ε
  | _, _::_, ε => contradiction
  | ε, _, _::_ => simp[lt]
  | _::_, _::_, _::_ => rw[lt] at *; exact h0.trans h1
}
end property
section relations
theorem ne.intro{x y:Digits}(h:¬x =L y):x ≠L y:=by{
  match x, y with
  | ε, ε => simp[eq] at h
  | ε, _::_
  | _::_, ε => simp[ne]
  | _::_, _::_ => rw[eq] at h; rw[ne]; exact intro h
}

theorem ne.elim{x y:Digits}(h:x ≠L y):¬x =L y:=by{
  match x, y with
  | ε, _::_
  | _::_, ε => simp[eq]
  | _::_, _::_ => rw[ne] at h; rw[eq]; exact h.elim
}

theorem ne_iff_not_eq{x y:Digits}:x ≠L y ↔ ¬x =L y:=
  Iff.intro ne.elim ne.intro

theorem eq.to_le{x y:Digits}(h:x =L y):x ≤L y:=by{
  match x, y with
  | ε, ε => simp[le]
  | _::_, _::_ => rw[eq] at h; rw[le]; exact h.to_le
}

theorem lt.to_le{x y:Digits}(h:x <L y):x ≤L y:=by{
  match x, y with
  | ε, _::_ => simp[le]
  | _::_, _::_ => rw[lt] at h; rw[le]; exact h.to_le
}

theorem le.to_eq_or_lt{x y:Digits}(h:x ≤L y):x =L y ∨ x <L y:=by{
  match x, y with
  | ε, ε => apply Or.inl; simp[eq]
  | ε, _::_ => apply Or.inr; simp[lt]
  | _::_, _::_ => rw[le] at h; rw[eq, lt]; exact h.to_eq_or_lt
}

theorem le_iff_eq_or_lt{x y:Digits}:x ≤L y ↔ x =L y ∨ x <L y:=
  Iff.intro le.to_eq_or_lt (by{
    intro h
    cases h with
    | inl h => exact h.to_le
    | inr h => exact h.to_le
  })

theorem lt.to_ne{x y:Digits}(h:x <L y):x ≠L y:=by{
  match x, y with
  | ε, _::_ => simp[ne]
  | _::_, _::_ => rw[lt] at h; rw[ne]; exact h.to_ne
}

theorem lt_of_le_of_ne{x y:Digits}(h0:x ≤L y)(h1:x ≠L y):x <L y:=by{
  match x, y with
  | ε, _::_ => simp[lt]
  | _::_, _::_ => rw[le] at h0; rw[ne] at h1; rw[lt]; exact lt_of_le_of_ne h0 h1
}

theorem lt_iff_le_and_ne{x y:Digits}:x <L y ↔ x ≤L y ∧ x ≠L y:=by{
  apply Iff.intro
  . {
    intro h
    exact And.intro h.to_le h.to_ne
  }
  . {
    intro h
    exact lt_of_le_of_ne h.left h.right
  }
}
end relations
section decidable
@[inline] instance eq.instDecidable:Decidable (x =L y):=
  match x, y with
  | ε, ε => instDecidableTrue
  | ε, _::_
  | _::_, ε => instDecidableFalse
  | _::_, _::_ => by{
    rw[eq]
    exact instDecidable
  }

@[inline] instance ne.instDecidable:Decidable (x ≠L y):=by{
  rw[ne_iff_not_eq]
  exact instDecidableNot
}

@[inline] instance le.instDecidable:Decidable (x ≤L y):=
  match x, y with
  | ε, ε
  | ε, _::_ => instDecidableTrue
  | _::_, ε => instDecidableFalse
  | _::_, _::_ => by{
    rw[le]
    exact instDecidable
  }

@[inline] instance lt.instDecidable:Decidable (x <L y):=by{
  rw[lt_iff_le_and_ne]
  exact instDecidableAnd
}
end decidable
section total
theorem eq_or_ne(x y:Digits):x =L y ∨ x ≠L y:=by{
  cases Decidable.em (x =L y) with
  | inl h => exact Or.inl h
  | inr h => exact Or.inr (ne.intro h)
}

theorem le.to_not_gt{x y:Digits}(h:y ≤L x):¬x <L y:=by{
  intro h'
  cases h.to_eq_or_lt with
  | inl h => exact h'.to_ne.symm.elim h
  | inr h => exact h'.asymm h
}

theorem lt.to_not_ge{x y:Digits}(h:y <L x):¬x ≤L y:=by{
  intro h'
  exact h'.to_not_gt h
}

theorem le_of_not_gt{x y:Digits}(h:¬y <L x):x ≤L y:=by{
  match x, y with
  | _::_, ε => simp[lt] at h
  | ε, ε
  | ε, _::_ => simp[le]
  | _::_, _::_ => rw[lt] at h; rw[le]; exact le_of_not_gt h
}

theorem lt_of_not_ge{x y:Digits}(h:¬y ≤L x):x <L y:=by{
  apply Decidable.of_not_not
  intro h'
  exact h (le_of_not_gt h')
}

theorem lt_iff_not_ge{x y:Digits}:x <L y ↔ ¬y ≤L x:=
  Iff.intro lt.to_not_ge lt_of_not_ge

theorem le_iff_not_gt{x y:Digits}:x ≤L y ↔ ¬y <L x:=
  Iff.intro le.to_not_gt le_of_not_gt

theorem le.total(x y:Digits):x ≤L y ∨ y ≤L x:=by{
  cases Decidable.em (x ≤L y) with
  | inl h => exact Or.inl h
  | inr h => exact Or.inr (lt_of_not_ge h).to_le
}

theorem le_or_gt(x y:Digits):x ≤L y ∨ y <L x:=by{
  cases Decidable.em (x ≤L y) with
  | inl h => exact Or.inl h
  | inr h => exact Or.inr (lt_of_not_ge h)
}

theorem trichotomous(x y:Digits):x <L y ∨ x =L y ∨ y <L x:=by{
  cases le_or_gt y x with
  | inl h => {
    apply Or.inr
    rw[le_iff_eq_or_lt] at h
    cases h with
    | inl h => exact Or.inl h.symm
    | inr h => exact Or.inr h
  }
  | inr h => exact Or.inl h
}

theorem lt_or_gt_of_ne{x y:Digits}(h:x ≠L y):x <L y ∨ y <L x:= by{
  rw[ne_iff_not_eq] at h
  have h':=trichotomous x y
  simp[h] at h'
  exact h'
}
end total
section trans
theorem ne_of_eq_of_ne{x y z:Digits}(h0:x =L y)(h1:y ≠L z):x ≠L z:=by{
  apply ne.intro
  intro h2
  exact h1.elim (h0.symm.trans h2)
}

theorem ne_of_ne_of_eq{x y z:Digits}(h0:x ≠L y)(h1:y =L z):x ≠L z:=by{
  apply ne.intro
  intro h2
  exact h0.elim (h2.trans h1.symm)
}

theorem le_of_eq_of_le{x y z:Digits}(h0:x =L y)(h1:y ≤L z):x ≤L z:=
  h0.to_le.trans h1

theorem le_of_le_of_eq{x y z:Digits}(h0:x ≤L y)(h1:y =L z):x ≤L z:=
  h0.trans h1.to_le

theorem lt_of_eq_of_lt{x y z:Digits}(h0:x =L y)(h1:y <L z):x <L z:=by{
  rw[lt_iff_not_ge]
  intro h
  exact h1.to_not_ge (le_of_le_of_eq h h0)
}

theorem lt_of_le_of_lt{x y z:Digits}(h0:x ≤L y)(h1:y <L z):x <L z:=by{
  cases h0.to_eq_or_lt with
  | inl h0 => exact lt_of_eq_of_lt h0 h1
  | inr h0 => exact h0.trans h1
}

theorem lt_of_lt_of_eq{x y z:Digits}(h0:x <L y)(h1:y =L z):x <L z:=by{
  rw[lt_iff_not_ge]
  intro h
  exact h0.to_not_ge (le_of_eq_of_le h1 h)
}

theorem lt_of_lt_of_le{x y z:Digits}(h0:x <L y)(h1:y ≤L z):x <L z:=by{
  cases h1.to_eq_or_lt with
  | inl h1 => exact lt_of_lt_of_eq h0 h1
  | inr h1 => exact h0.trans h1
}
end trans
section zero
theorem ε_unique{x:Digits}(h:x =L nil):x = nil:=by{
  match x with
  | ε => rfl
}

theorem ε_le(x:Digits):ε ≤L x:=by{
  match x with
  | ε
  | _::_ => simp[le]
}

theorem not_lt_ε(x:Digits):¬x <L ε:=by{
  match x with
  | ε
  | _::_ => simp[lt]
}

theorem ε_lt_not_ε{x:Digits}(h:x≠ε):ε<Lx:=by{
  have h:ε≠Lx:=by{
    apply ne.intro
    intro h
    have h:=ε_unique h.symm
    contradiction
  }
  exact lt_of_le_of_ne (ε_le _) h
}

theorem le_ε_eq_ε{x:Digits}(h:x ≤L ε):x =L ε:=by{
  rw[le_iff_eq_or_lt] at h
  simp[not_lt_ε] at h
  exact h
}

theorem le_ε_is_ε{x:Digits}(h:x ≤L ε):x = ε:=
  ε_unique (le_ε_eq_ε h)
end zero
section step
theorem lt_cons(x:Digits)(d:Digit):x <L x::d:=by{
  induction x generalizing d with
  | nil => simp[lt]
  | cons xs xd ih => simp[lt]; exact ih xd
}

theorem le_cons(x:Digits)(d:Digit):x ≤L x::d:=
  (lt_cons x d).to_le
end step
theorem eq.from_strict_eq{x y:Digits}(h:x = y):x =L y:=by{
  simp[h,eq.refl]
}
theorem ne.to_strict_ne{x y:Digits}(h:x ≠L y):x ≠ y:=by{
  intro h'
  rw[h'] at h
  simp[ne.irrefl] at h
}
end len
end Digits

end wkmath
