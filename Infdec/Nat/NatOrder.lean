import Infdec.Nat.StdNat

namespace wkmath
namespace Digits
namespace nat

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
  - le.to_eq_or_lt √
  - le_iff_eq_or_lt √
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
  - zero_le √
  - not_lt_zero √
  - zero_lt_notzero √
  - le_zero_isZero
-/
section defines
def ne:Digits → Digits → Prop
  | ε, ε => False
  | ε, ds::d
  | ds::d, ε => ¬(ds::d).isZero
  | xs::xd, ys::yd => ne xs ys ∨ xd ≠ yd

notation:50 lhs:51 " ≠N " rhs:51 => ne lhs rhs

def lt:Digits → Digits → Prop
  | ε, ε
  | _::_, ε => False
  | ε, ds::d => ¬(ds::d).isZero
  | xs::xd, ys::yd => lt xs ys ∨ (xd < yd ∧ xs =N ys)

notation:50 lhs:51 " < " rhs:51 => lt lhs rhs

def le:Digits → Digits → Prop
  | ε, ε
  | ε, _::_ => True
  | ds::d, ε => (ds::d).isZero
  | xs::xd, ys::yd => lt xs ys ∨ (xd ≤ yd ∧ xs =N ys)

notation:50 lhs:51 " ≤ " rhs:51 => le lhs rhs
end defines
section decidable
@[inline] instance ne.instDecidable{x y:Digits}:Decidable (x≠Ny):=
  match x, y with
  | ε, ε => instDecidableFalse
  | ε, _::_
  | _::_, ε => instDecidableNot
  | x::_, y::_ =>
    have : Decidable (x ≠N y) := instDecidable
    instDecidableOr
@[inline] instance lt.instDecidable{x y:Digits}:Decidable (x < y):=
  match x, y with
  | ε, ε
  | _::_, ε => instDecidableFalse
  | ε, _::_ => instDecidableNot
  | xs::_, ys::_ =>
    have : Decidable (xs < ys) := instDecidable
    instDecidableOr
@[inline] instance le.instDecidable{x y:Digits}:Decidable (x ≤ y):=
  match x, y with
  | ε, ε
  | ε, _::_ => instDecidableTrue
  | _::_, ε => isZero.instDecidable
  | _::_, _::_ => instDecidableOr
end decidable
section relations
theorem ne.intro{x y:Digits}(h:¬x =N y):x ≠N y:=by{
  match x, y with
  | ε, ε => simp[eq] at h
  | ε, _::_
  | _::_, ε => simp[ne]; simp[eq] at h; exact h
  | x'::_, y'::_ => {
    rw[eq] at h
    rw[ne]
    cases Decidable.em (x'=Ny') with
    | inl h' => simp[h'] at h;simp[h]
    | inr h' => exact Or.inl (intro h')
  }
}

theorem ne.elim{x y:Digits}(h:x ≠N y):¬x =N y:=by{
  match x, y with
  | ε, _::_
  | _::_, ε => simp[eq]; simp[ne] at h; exact h
  | _::_, _::_ => {
    rw[ne] at h
    rw[eq]
    cases h with
    | inl h => simp[h.elim]
    | inr h => simp[h]
  }
}

theorem ne_iff_not_eq{x y:Digits}:x ≠N y ↔ ¬x =N y:=
  Iff.intro ne.elim ne.intro

theorem eq.to_le{x y:Digits}(h:x =N y):x ≤ y:=by{
  match x, y with
  | ε, ε
  | ε, _::_ => simp[le]
  | _::_, ε => simp[le];exact h
  | _::_, _::_ => {
    simp[le]
    simp[eq] at h
    apply Or.inr
    rw[h.right]
    exact And.intro (Digit.le.refl _) h.left
  }
}

theorem lt.to_le{x y:Digits}(h:x < y):x ≤ y:=by{
  match x, y with
  | ε, ε
  | _::_, ε => contradiction
  | ε, _::_ => simp[le]
  | _::_, _::_ => {
    simp[lt] at h
    simp[le]
    cases h with
    | inl h => exact Or.inl h
    | inr h => exact Or.inr (And.intro h.left.to_le h.right)
  }
}

theorem le.to_eq_or_lt{x y:Digits}(h:x ≤ y):x =N y ∨ x < y:=by{
  match x, y with
  | ε, ε => simp
  | ε, _::_ => {
    simp[eq, lt]
    exact Decidable.em (isZero _)
  }
  | _::_, ε => {
    simp[le] at h
    simp[eq]
    exact Or.inl h
  }
  | _::_, _::_ => {
    simp[le] at h
    cases h with
    | inl h => {
      apply Or.inr
      simp[lt]
      exact Or.inl h
    }
    | inr h => {
      simp[eq, lt]
      have hl:=h.left.to_eq_or_lt
      cases hl with
      | inl hl => exact Or.inl (And.intro h.right hl)
      | inr hl => {
        apply Or.inr
        apply Or.inr
        exact And.intro hl h.right
      }
    }
  }
}

theorem le_iff_eq_or_lt{x y:Digits}:x ≤ y ↔ x =N y ∨ x < y:=
  Iff.intro le.to_eq_or_lt (by{
    intro h
    cases h with
    | inl h
    | inr h => exact h.to_le
  })

theorem lt.to_ne{x y:Digits}(h:x < y):x ≠N y:=by{
  match x, y with
  | ε, ε
  | _::_, ε => contradiction
  | ε, _::_ => simp[ne]; simp[lt] at h; exact h
  | _::_, _::_ => {
    simp[ne]
    simp[lt] at h
    cases h with
    | inl h => exact Or.inl h.to_ne
    | inr h => {
      exact Or.inr h.left.to_ne
    }
  }
}

theorem lt_of_le_of_ne{x y:Digits}(h0:x ≤ y)(h1:x ≠N y):x < y:=by{
  match x, y with
  | ε, ε => contradiction
  | ε, _::_ => simp[lt]; simp[ne] at h1; exact h1
  | _::_, ε => simp[le] at h0; simp[ne] at h1; contradiction
  | _::_, _::_ => {
    simp[le] at h0
    simp[ne] at h1
    simp[lt]
    cases h0 with
    | inl h0 => exact Or.inl h0
    | inr h0 => cases h1 with
      | inl h1 => have h0:=h0.right; have h1:=h1.elim; contradiction
      | inr h1 => {
        apply Or.inr
        simp[h0.right]
        exact Digit.lt_of_le_of_ne h0.left h1
      }
  }
}

theorem lt_iff_le_and_ne{x y:Digits}:x < y ↔ x ≤ y ∧ x ≠N y:=
  Iff.intro (by{
    intro h
    exact And.intro h.to_le h.to_ne
  }) (by{
    intro ⟨hl,hr⟩
    exact lt_of_le_of_ne hl hr
  })
end relations
section zero
theorem ε_le(x:Digits):ε ≤ x:=by{
  cases x with
  | nil
  | cons _ _ => simp[le]
}

theorem zero_le{x:Digits}(y:Digits)(h:x.isZero):x ≤ y:=by{
  induction x generalizing y with
  | nil => exact ε_le y
  | cons xs xd ih => {
    match y with
    | ε => simp[le]; exact h
    | ys::yd => {
      simp[le]
      have ih:=ih ys h.left
      cases ih.to_eq_or_lt with
      | inl ih => {
        apply Or.inr
        rw[h.right]
        exact And.intro yd.zero_le ih
      }
      | inr ih => exact Or.inl ih
    }
  }
}

theorem ε_lt_notzero{x:Digits}(h:¬x.isZero):ε<x:=by{
  rw[lt_iff_le_and_ne]
  rw[ne_iff_not_eq]
  apply And.intro (ε_le x)
  intro h'
  apply h
  exact nat_eq_zero_isZero h' ε_isZero
}

theorem zero_lt_notzero{x y:Digits}(hx:x.isZero)(hy:¬y.isZero):x < y:=by{
  rw[lt_iff_le_and_ne]
  rw[ne_iff_not_eq]
  apply And.intro (zero_le y hx)
  intro h
  apply hy
  exact nat_eq_zero_isZero h hx
}

theorem not_lt_ε(x:Digits):¬x < ε :=by{
  match x with
  | ε
  | _::_ => simp[lt]
}

theorem not_lt_zero(x:Digits){y:Digits}(h:y.isZero):¬x < y:=by{
  match x, y with
  | ε, ε
  | _::_, ε => simp[lt]
  | ε, _::_ => simp[lt];intro _; contradiction
  | x'::d, y'::_ => {
    intro h'
    simp[lt] at h'
    cases h' with
    | inl h' => exact not_lt_zero x' h.left h'
    | inr h' => rw[h.right] at h'; apply Digit.not_lt_zero d; exact h'.left
  }
}

theorem lt_not_zero{x y:Digits}(h:x < y):¬y.isZero:=by{
  intro h'
  exact not_lt_zero x h' h
}

theorem le_ε_isZero{x:Digits}(h:x ≤ ε):x.isZero:=by{
  rw[le_iff_eq_or_lt] at h
  simp[not_lt_ε] at h
  exact nat_eq_zero_isZero' h ε_isZero
}
end zero
section properties
theorem ne.irrefl(x:Digits):¬x ≠N x:=by{
  induction x with
  | nil => simp[ne]
  | cons _ _ ih => rw[ne] at *; simp[ih]
}

theorem ne.symm{x y:Digits}(h:x ≠N y):y ≠N x:=by{
  match x, y with
  | _::_, ε
  | ε, _::_ => simp[ne] at *; exact h
  | _::_, _::_ => {
    rw[ne] at *
    cases h with
    | inl h => exact Or.inl h.symm
    | inr h => exact Or.inr h.symm
  }
}

theorem lt.irrefl(x:Digits):¬x<x:=by{
  induction x with
  | nil => simp
  | cons xs xd ih => {
    simp[lt,Digit.lt.irrefl]
    exact ih
  }
}

theorem lt.asymm{x y:Digits}(h:x < y):¬y < x:=by{
  match x, y with
  | ε, ε
  | _::_, ε => contradiction
  | ε, _::_ => simp[lt]
  | _::_, _::_ => {
    simp[lt] at *
    intro h'
    cases h with
    | inl h => {
      cases h' with
      | inl h' => exact h.asymm h'
      | inr h' => {
        have h:=h.to_ne.elim
        have h':=h'.right.symm
        contradiction
      }
    }
    | inr h => {
      cases h' with
      | inl h' => {
        have h':=h'.to_ne.elim
        have h:=h.right.symm
        contradiction
      }
      | inr h' => exact h.left.asymm h'.left
    }
  }
}

theorem le.refl(x:Digits):x ≤ x:=
  (eq.refl x).to_le

theorem le.antisymm{x y:Digits}(h0:x ≤ y)(h1:y ≤ x):x =N y:=by{
  match x, y with
  | ε, ε => simp
  | ε, _::_
  | _::_, ε => simp[le] at *; simp[eq]; simp[h0, h1]
  | _::_, _::_ => {
    simp[le] at *
    simp[eq]
    cases h0 with
    | inl h0 => {
      have h2:=h0.asymm
      simp[h2] at h1
      have h0:=h0.to_ne.elim
      have h1:=h1.right.symm
      contradiction
    }
    | inr h0 => {
      cases h1 with
      | inl h1 => {
        have h1:=h1.to_ne.elim
        have h0:=h0.right.symm
        contradiction
      }
      | inr h1 => {
        exact And.intro h0.right (h0.left.antisymm h1.left)
      }
    }
  }
}
end properties
section trans
theorem ne_of_ne_of_eq{x y z:Digits}(h0:x ≠N y)(h1:y =N z):x ≠N z:=by{
  apply ne.intro
  intro h
  exact h0.elim (h.trans h1.symm)
}

theorem ne_of_eq_of_ne{x y z:Digits}(h0:x =N y)(h1:y ≠N z):x ≠N z:=by{
  apply ne.intro
  intro h
  exact h1.elim (h0.symm.trans h)
}

theorem lt_of_lt_of_eq{x y z:Digits}(h0:x < y)(h1:y =N z):x < z:=by{
  match x, y, z with
  | x, ε, _ => have := not_lt_ε x; contradiction
  | x, _::_, ε => have := not_lt_zero x (nat_eq_zero_isZero' h1 ε_isZero); contradiction
  | ε, _::_, _::_ => {
    simp[lt] at *
    intro h
    apply h0
    exact nat_eq_zero_isZero' h1 h
  }
  | _::_, _::_, _::_ => {
    simp[lt] at *
    simp[eq] at h1
    rw[h1.right] at h0
    have h1:=h1.left
    cases h0 with
    | inl h0 => exact Or.inl (lt_of_lt_of_eq h0 h1)
    | inr h0 => {
      apply Or.inr
      apply And.intro h0.left
      exact h0.right.trans h1
    }
  }
}

theorem lt_of_eq_of_lt{x y z:Digits}(h0:x =N y)(h1:y < z):x < z:=by{
  match x, y, z with
  | _, y, ε => have := not_lt_ε y; contradiction
  | x, ε, _::_ => {
    have h:=nat_eq_zero_isZero' h0 ε_isZero
    have h':=lt_not_zero h1
    exact zero_lt_notzero h h'
  }
  | ε, _::_, _::_ => {
    have h':=lt_not_zero h1
    exact ε_lt_notzero h'
  }
  | _::_, _::_, _::_ => {
    simp[lt] at *
    rw[eq] at *
    rw[h0.right]
    cases h1 with
    | inl h1 => exact Or.inl (lt_of_eq_of_lt h0.left h1)
    | inr h1 => apply Or.inr; apply And.intro h1.left;exact h0.left.trans h1.right
  }
}

theorem lt.trans{x y z:Digits}(h0:x < y)(h1:y < z):x < z:=by{
  match x, y, z with
  | x, ε, _ => have := not_lt_ε x; contradiction
  | _, y, ε => have := not_lt_ε y; contradiction
  | ε, _::_, _::_ => apply zero_lt_notzero ε_isZero; exact lt_not_zero h1
  | _::_, _::_, _::_ => {
    simp[lt] at *
    cases h0 with
    | inl h0 => cases h1 with
      | inl h1 => exact Or.inl (h0.trans h1)
      | inr h1 => exact Or.inl (lt_of_lt_of_eq h0 h1.right)
    | inr h0 => cases h1 with
      | inl h1 => exact Or.inl (lt_of_eq_of_lt h0.right h1)
      | inr h1 => exact Or.inr (And.intro (h0.left.trans h1.left) (h0.right.trans h1.right))
  }
}

theorem le.trans{x y z:Digits}(h0:x ≤ y)(h1:y ≤ z):x ≤ z:=by{
  rw[le_iff_eq_or_lt] at *
  cases h0 with
  | inl h0 => cases h1 with
    | inl h1 => exact Or.inl (h0.trans h1)
    | inr h1 => exact Or.inr (lt_of_eq_of_lt h0 h1)
  | inr h0 => cases h1 with
    | inl h1 => exact Or.inr (lt_of_lt_of_eq h0 h1)
    | inr h1 => exact Or.inr (h0.trans h1)
}

theorem le_of_eq_of_le{x y z:Digits}(h0:x =N y)(h1:y ≤ z):x ≤ z:=
  h0.to_le.trans h1

theorem le_of_le_of_eq{x y z:Digits}(h0:x ≤ y)(h1:y =N z):x ≤ z:=
  h0.trans h1.to_le

theorem lt_of_le_of_lt{x y z:Digits}(h0:x ≤ y)(h1:y < z):x < z:=by{
  rw[le_iff_eq_or_lt] at h0
  cases h0 with
  | inl h0 => exact lt_of_eq_of_lt h0 h1
  | inr h0 => exact h0.trans h1
}

theorem lt_of_lt_of_le{x y z:Digits}(h0:x < y)(h1:y ≤ z):x < z:=by{
  rw[le_iff_eq_or_lt] at h1
  cases h1 with
  | inl h1 => exact lt_of_lt_of_eq h0 h1
  | inr h1 => exact h0.trans h1
}
end trans
section total
theorem eq_or_ne(x y:Digits):x =N y ∨ x ≠N y:=by{
  rw[ne_iff_not_eq]
  exact Decidable.em (x =N y)
}

theorem lt.to_not_ge{x y:Digits}(h:x < y):¬y ≤ x:=by{
  intro h'
  rw[le_iff_eq_or_lt] at h'
  cases h' with
  | inl h' => have h:=lt_of_lt_of_eq h h'; simp[lt.irrefl] at h
  | inr h' => exact h.asymm h'
}

theorem le.to_not_gt{x y:Digits}(h:x ≤ y):¬y < x:=by{
  rw[le_iff_eq_or_lt] at h
  cases h with
  | inl h => intro h'; exact h'.to_ne.elim h.symm
  | inr h => exact h.asymm
}

theorem le_of_not_gt{x y:Digits}(h:¬x < y):y ≤ x:=by{
  match x, y with
  | ε, ε
  | _::_, ε => simp[le]
  | ε, _::_ => simp[lt] at h;have h:=Decidable.of_not_not h; simp[le]; exact h
  | x'::xd, y'::yd => {
    simp[le]
    simp[lt] at h
    have h':¬x'<y':=by{
      cases Decidable.em (x'<y') with
      | inl h' => simp[h'] at h
      | inr h' => exact h'
    }
    simp[h'] at h
    have h:¬xd < yd ∨ ¬x' =N y':=by{
      cases Decidable.em (xd < yd) with
      | inl h'' => simp[h''] at h; exact Or.inr h
      | inr h'' => exact Or.inl h''
    }
    have h':=le_of_not_gt h'
    rw[le_iff_eq_or_lt] at h'
    cases h with
    | inl h => {
      have h:=Digit.le_of_not_gt h
      cases h' with
      | inl h' => apply Or.inr; exact And.intro h h'
      | inr h' => apply Or.inl h'
    }
    | inr h => {
      apply Or.inl
      have h:=(ne.intro h).symm.elim
      simp[h] at h'
      exact h'
    }
  }
}

theorem lt_of_not_ge{x y:Digits}(h:¬y ≤ x):x < y:=by{
  rw[le_iff_eq_or_lt] at h
  have h:¬y =N x ∧ ¬y < x:=by{
    apply And.intro
    . {
      intro h'
      apply h
      exact Or.inl h'
    }
    . {
      intro h'
      apply h
      exact Or.inr h'
    }
  }
  exact lt_of_le_of_ne (le_of_not_gt h.right) (ne.intro h.left).symm
}

theorem lt_iff_not_ge{x y:Digits}:x < y ↔ ¬ y ≤ x:=
  Iff.intro lt.to_not_ge lt_of_not_ge

theorem le_iff_not_gt{x y:Digits}:x ≤ y ↔ ¬ y < x:=
  Iff.intro le.to_not_gt le_of_not_gt

theorem le_or_gt(x y:Digits):x ≤ y ∨ y < x:=by{
  have h:=Decidable.em (x ≤ y)
  rw[←lt_iff_not_ge] at h
  exact h
}

theorem le.total(x y:Digits):x ≤ y ∨ y ≤ x:=by{
  have h:=le_or_gt x y
  cases h with
  | inl h => exact Or.inl h
  | inr h => exact Or.inr h.to_le
}

theorem lt_or_gt_of_ne{x y:Digits}(h:x ≠N y):x < y ∨ y < x:=by{
  have h':=le_or_gt x y
  rw[le_iff_eq_or_lt] at h'
  rw[ne_iff_not_eq] at h
  simp[h] at h'
  exact h'
}

theorem trichotomous(x y:Digits):x < y ∨ x =N y ∨ y < x:=by{
  have h:=le_or_gt x y
  rw[le_iff_eq_or_lt] at h
  cases h with
  | inl h => cases h with
    | inl h => apply Or.inr; apply Or.inl; exact h
    | inr h => apply Or.inl; exact h
  | inr h => apply Or.inr; apply Or.inr; exact h
}
end total

theorem le_zero_isZero{x y:Digits}(h0:x ≤ y)(h1:y.isZero):x.isZero:=
  le_ε_isZero (nat.le_of_le_of_eq h0 (zero_nat_eq_zero h1 ε_isZero))

theorem not_zero_lt_cons{x:Digits}(h:¬x.isZero)(d:Digit):x < x::d:=by{
  induction x generalizing d with
  | nil => contradiction
  | cons x' d' ih => {
    rw[isZero] at h
    rw[de_morgan_not_and] at h
    match d', d with
    | (0), (1)
    | (0), (2) => {
      simp[lt]
      simp at h
      exact Or.inl (ih h _)
    }
    | (1), (2) => {
      simp[lt]
      cases Decidable.em (x'.isZero) with
      | inl h' => {
        apply Or.inl
        cases x' with
        | nil => simp[lt]
        | cons x'' d'' => {
          rw[isZero] at h'
          rw[h'.right] at *
          rw[lt]
          apply Or.inr
          simp
          apply zero_nat_eq_zero h'.left
          simp[isZero]
          exact h'.left
        }
      }
      | inr h' => exact Or.inl (ih h' _)
    }
    | (0), (0) => {
      simp[lt]
      simp at h
      exact ih h _
    }
    | (1), (0)
    | (1), (1)
    | (2), (0)
    | (2), (1)
    | (2), (2) => {
      simp[lt]
      cases Decidable.em (x'.isZero) with
      | inl h' => {
        cases x' with
        | nil => simp[lt]
        | cons x'' d'' => {
          rw[isZero] at h'
          rw[h'.right] at *
          simp[lt]
          apply Or.comm
          rw[←le_iff_eq_or_lt]
          exact zero_le _ h'.left
        }
      }
      | inr h' => exact ih h' _
    }
  }
}

theorem le_cons(x:Digits)(d:Digit):x ≤ x::d:=
  (Decidable.em (x.isZero)).elim (λ h => zero_le _ h) (λ h => (not_zero_lt_cons h _).to_le)

end nat
end Digits
end wkmath
