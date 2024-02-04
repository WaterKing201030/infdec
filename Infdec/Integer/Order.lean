import Infdec.Integer.Base

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
  - ne.intro
  - ne.elim
  - ne_iff_not_eq bydef
  - eq.to_le √
  - lt.to_le √
  - le.to_eq_or_lt
  - le_iff_eq_or_lt bydef
  - lt.to_ne √
  - lt_of_le_of_ne √
  - lt_iff_le_and_ne √
- decidable √
- total √
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
- trans √
  - ne_of_eq_of_ne √
  - ne_of_ne_of_eq √
  - le_of_eq_of_le √
  - le_of_le_of_eq √
  - lt_of_eq_of_lt √
  - lt_of_lt_of_eq √
  - lt_of_le_of_lt √
  - lt_of_lt_of_le √
-/

namespace wkmath
namespace int
def eq(x y:int):=
  if x.digits.isZero then
    y.digits.isZero
  else
    x.digits =N y.digits ∧ x.negsign = y.negsign

def ne(x y:int):=
  ¬(eq x y)

def lt:int → int → Prop
  | ⟨x', false⟩, ⟨y', false⟩ => x' < y'
  | ⟨x', true⟩, ⟨y', true⟩ => y' < x'
  | ⟨x', true⟩, ⟨y', false⟩ => ¬(x'.isZero ∧ y'.isZero)
  | ⟨_, false⟩, ⟨_, true⟩ => False

def le(x y:int):=
  eq x y ∨ lt x y

notation:50 lhs:51 " =I " rhs:51 => eq lhs rhs
notation:50 lhs:51 " ≠I " rhs:51 => ne lhs rhs
notation:50 lhs:51 " < " rhs:51 => lt lhs rhs
notation:50 lhs:51 " ≤ " rhs:51 => le lhs rhs

theorem nat_ne_to_int_ne{x y:int}(h:x.digits ≠N y.digits):x ≠I y:=by{
  have h:=h.elim
  intro h'
  cases Decidable.em (x.digits.isZero) with
  | inl h'' => {
    simp[eq, h''] at h'
    exact h (Digits.zero_nat_eq_zero h'' h')
  }
  | inr h'' => {
    simp[eq, h''] at h'
    exact h h'.left
  }
}

theorem int_eq_to_nat_eq{x y:int}(h:x =I y):x.digits =N y.digits:=by{
  cases Decidable.em (x.digits.isZero) with
  | inl h' => {
    simp[eq, h'] at h
    exact Digits.zero_nat_eq_zero h' h
  }
  | inr h' => {
    simp[eq, h'] at h
    exact h.left
  }
}

theorem notsame_sign_eq_to_zero{x y:int}(h0:x =I y)(h1:x.negsign ≠ y.negsign):x.digits.isZero ∧ y.digits.isZero:=by{
  cases Decidable.em (x.digits.isZero) with
  | inl h => {
    simp[eq, h] at h0
    exact And.intro h h0
  }
  | inr h => simp[eq,h,h1] at h0
}

theorem same_sign_eq_to_nat_eq{x y:int}(h0:x =I y)(h1:x.negsign = y.negsign):x.digits =N y.digits:=by{
  cases Decidable.em (x.digits.isZero) with
  | inl h => {
    simp[eq, h] at h0
    exact Digits.zero_nat_eq_zero h h0
  }
  | inr h => {
    simp[eq, h, h1] at h0
    exact h0
  }
}

section decidable
@[inline] instance instDecidableEq{x y:int}:Decidable (x = y):=
  match x, y with
  | ⟨x0, x1⟩, ⟨y0, y1⟩ => dite (x0 = y0 ∧ x1 = y1) (λ h => isTrue (by{rw[h.left, h.right]})) (λ h => isFalse (
    λ h' => int.noConfusion h' (λ p q => h (And.intro p q))
  ))

@[inline] instance eq.instDecidable{x y:int}:Decidable (x =I y):=
  instDecidableIteProp

@[inline] instance ne.instDecidable{x y:int}:Decidable (x ≠I y):=
  instDecidableNot

@[inline] instance lt.instDecidable{x y:int}:Decidable (x < y):=
  match x, y with
  | ⟨_, false⟩, ⟨_, false⟩
  | ⟨_, true⟩, ⟨_, true⟩ => Digits.nat.lt.instDecidable
  | ⟨_, true⟩, ⟨_, false⟩ => instDecidableNot
  | ⟨_, false⟩, ⟨_, true⟩ => instDecidableFalse

@[inline] instance le.instDecidable{x y:int}:Decidable (x ≤ y):=
  instDecidableOr
end decidable
section properties
theorem eq.refl(x:int):x =I x:=by{
  rw[eq]
  cases (Decidable.em (x.digits.isZero)) with
  | inl h => simp[h]
  | inr h => simp[h,Digits.nat.eq.refl]
}

theorem eq.symm{x y:int}(h:x =I y):y =I x:=by{
  rw[eq] at *
  cases (Decidable.em (x.digits.isZero)) with
  | inl h' => {
    simp[h'] at h
    simp[h]
    exact h'
  }
  | inr h' => {
    cases (Decidable.em (y.digits.isZero)) with
    | inl h'' => {
      simp[h'] at h
      exact (h' (Digits.nat_eq_zero_isZero' h.left h'')).elim
    }
    | inr h'' => {
      simp[h'']
      simp[h'] at h
      exact And.intro h.left.symm h.right.symm
    }
  }
}

theorem eq.symm_iff{x y:int}:x =I y ↔ y =I x:=
  Iff.intro (λ h => h.symm) (λ h => h.symm)

theorem eq.trans{x y z:int}(h0:x =I y)(h1:y =I z):x =I z:=by{
  rw[eq] at *
  cases (Decidable.em (x.digits.isZero)) with
  | inl h => {
    simp[h] at *
    simp[h0] at h1
    exact h1
  }
  | inr h => {
    simp[h]
    simp[h] at h0
    have h':=Digits.nat_eq_not_zero_isnot_zero h h0.left
    simp[h'] at h1
    exact And.intro (h0.left.trans h1.left) (h0.right.trans h1.right)
  }
}

theorem ne.irrefl(x:int):¬(x ≠I x):=
  λ h => h (eq.refl x)

theorem ne.symm{x y:int}(h:x ≠I y):y ≠I x:=
  λ h' => h h'.symm

theorem lt.irrefl(x:int):¬(x < x):=
  match x with | ⟨_,true⟩ | ⟨_,false⟩ => Digits.nat.lt.irrefl _

theorem lt.asymm{x y:int}(h:x < y):¬(y < x):=by{
  match x, y with
  | ⟨_, false⟩, ⟨_, false⟩
  | ⟨_, true⟩, ⟨_, true⟩ => simp[lt] at *; exact h.asymm
  | ⟨_, true⟩, ⟨_, false⟩
  | ⟨_, false⟩, ⟨_, true⟩ => simp[lt] at *
}

theorem le.refl(x:int):x ≤ x:=
  Or.inl (eq.refl x)
end properties
section relation
theorem eq.to_le{x y:int}(h:x =I y):x ≤ y:=
  Or.inl h

theorem lt.to_le{x y:int}(h:x < y):x ≤ y:=
  Or.inr h

theorem lt.to_ne{x y:int}(h:x < y):x ≠I y:=by{
  match x, y with
  | ⟨x', false⟩, ⟨y', false⟩ => {
    exact nat_ne_to_int_ne (by{
      simp[lt] at h
      exact h.to_ne
    })
  }
  | ⟨x, true⟩, ⟨y, true⟩ => {
    exact nat_ne_to_int_ne (by{
      simp[lt] at h
      exact h.to_ne.symm
    })
  }
  | ⟨x, true⟩, ⟨y, false⟩ => {
    simp[lt] at h
    cases Decidable.em (y.isZero) with
    | inl h' => {
      simp[h'] at h
      rw[ne]
      simp[eq, h]
    }
    | inr h' => {
      apply ne.symm
      rw[ne]
      simp[eq,h']
    }
  }
}

theorem lt_of_le_of_ne{x y:int}(h0:x ≤ y)(h1:x ≠I y):x < y:=by{
  rw[le] at h0
  rw[ne] at h1
  simp[h1] at h0
  exact h0
}

theorem lt_iff_le_and_ne{x y:int}:x < y ↔ (x ≤ y ∧ x ≠I y):=
  Iff.intro (λ h => And.intro h.to_le h.to_ne) (λ h => lt_of_le_of_ne h.left h.right)
end relation
section total
theorem eq_or_ne(x y:int):x =I y ∨ x ≠I y:=
  Decidable.em (x =I y)

theorem not_lt_of_ge{x y:int}(h:x ≤ y):¬y < x:=by{
  rw[le] at h
  intro h'
  cases h with
  | inl h => exact h'.to_ne h.symm
  | inr h => exact h'.asymm h
}

theorem not_le_of_gt{x y:int}(h:x < y):¬y ≤ x:=
  de_morgan_not_or.mpr (And.intro h.to_ne.symm h.asymm)

theorem lt_of_not_ge{x y:int}(h:¬x ≤ y):y < x:=by{
  rw[le] at h
  have h:=de_morgan_not_or.mp h
  match x, y with
  | ⟨x0, false⟩, ⟨y0, false⟩ => {
    simp[eq,lt] at *
    cases Decidable.em (x0.isZero) with
    | inl h' => {
      simp[h'] at h
      exact (h.right (Digits.nat.zero_lt_notzero h' h.left)).elim
    }
    | inr h' => {
      simp[h'] at h
      rw[←de_morgan_not_or] at h
      rw[←Digits.nat.le_iff_eq_or_lt] at h
      exact Digits.nat.lt_of_not_ge h
    }
  }
  | ⟨x0, true⟩, ⟨y0, true⟩ => {
    simp[eq,lt] at *
    cases Decidable.em (x0.isZero) with
    | inl h' => {
      simp[h'] at h
      exact Digits.nat.zero_lt_notzero h' h.left
    }
    | inr h' => {
      simp[h'] at h
      rw[←de_morgan_not_or] at h
      rw[Digits.nat.eq.symm_iff] at h
      rw[←Digits.nat.le_iff_eq_or_lt] at h
      exact Digits.nat.lt_of_not_ge h
    }
  }
  | ⟨x0, true⟩, ⟨y0, false⟩ => {
    simp[eq, lt] at *
    cases Decidable.em (x0.isZero) with
    | inl h' => {
      simp[h'] at h
      rw[not_not_iff] at h
      exact h.left h.right
    }
    | inr h' => simp[h'] at h
  }
  | ⟨x0, false⟩, ⟨x1, true⟩ => {
    simp[eq, lt] at *
    cases Decidable.em (x0.isZero) with
    | inl h' => {
      simp[h'] at h
      simp[h]
    }
    | inr h' => simp[h']
  }
}

theorem lt_iff_not_ge{x y:int}:x < y ↔ ¬y ≤ x:=
  Iff.intro not_le_of_gt lt_of_not_ge

theorem le_of_not_gt{x y:int}(h:¬x < y):y ≤ x:=by{
  rw[lt_iff_not_ge] at h
  exact Decidable.of_not_not h
}

theorem le_iff_not_gt{x y:int}:x ≤ y ↔ ¬y < x:=
  Iff.intro not_lt_of_ge le_of_not_gt

theorem le_or_gt(x y:int):x ≤ y ∨ y < x:=
  (Decidable.em (x ≤ y)).elim (λ h => Or.inl h) (λ h => Or.inr (lt_of_not_ge h))

theorem le.total(x y:int):x ≤ y ∨ y ≤ x:=
  (le_or_gt x y).elim (λ h => Or.inl h) (λ h => Or.inr h.to_le)

theorem lt_or_gt_of_ne{x y:int}(h:x ≠I y):x < y ∨ y < x:=by{
  have h':=le_or_gt x y
  rw[le] at h'
  rw[ne] at h
  simp[h] at h'
  exact h'
}

theorem trichotomous(x y:int):x < y ∨ x =I y ∨ y < x:=by{
  have h:=le_or_gt x y
  rw[le] at h
  rw[Or.comm_iff (x =I y)] at h
  rw[Or.assoc_iff] at h
  exact h
}
end total
section properties
theorem le.antisymm{x y:int}(h0:x ≤ y)(h1:y ≤ x):x =I y:=
  h0.elim (λ h => h) (λ h => h1.elim (λ h' => h'.symm) (λ h' => (h.asymm h').elim))

theorem lt.trans{x y z:int}(h0:x < y)(h1:y < z):x < z:=by{
  match x, y, z with
  | ⟨_, false⟩, ⟨_, true⟩, _
  | _, ⟨_, false⟩, ⟨_, true⟩ => contradiction
  | ⟨_, false⟩, ⟨_, false⟩, ⟨_, false⟩ => simp[lt] at *; exact h0.trans h1
  | ⟨_, true⟩, ⟨_, true⟩, ⟨_, true⟩ => simp[lt] at *; exact h1.trans h0
  | ⟨_, true⟩, ⟨_, false⟩, ⟨_, false⟩ => {
    simp[lt] at *
    rw[de_morgan_not_and] at *
    exact Or.inr (Digits.nat.lt_not_zero h1)
  }
  | ⟨_, true⟩, ⟨_, true⟩, ⟨_, false⟩ => {
    simp[lt] at *
    rw[de_morgan_not_and] at *
    exact Or.inl (Digits.nat.lt_not_zero h0)
  }
}
end properties
section trans
theorem ne_of_eq_of_ne{x y z:int}(h0:x =I y)(h1:y ≠I z):x ≠I z:=
  λ h2 => h1 (h0.symm.trans h2)

theorem ne_of_ne_of_eq{x y z:int}(h0:x ≠I y)(h1:y =I z):x ≠I z:=
  λ h2 => h0 (h2.trans h1.symm)

theorem lt_of_eq_of_lt{x y z:int}(h0:x =I y)(h1:y < z):x < z:=by{
  cases Decidable.em (x.negsign = y.negsign) with
  | inl h => {
    have h0:(x.digits) =N (y.digits):=by{
      apply same_sign_eq_to_nat_eq
      exact h0
      exact h
    }
    match x, y, z with
    | ⟨_, _⟩, ⟨_, false⟩, ⟨_, true⟩ => contradiction
    | ⟨_, _⟩, ⟨_, true⟩, ⟨_, false⟩ => {
      simp[h] at *
      rw[h]
      simp[lt] at *
      rw[de_morgan_not_and] at *
      exact h1.elim (λ h' => Or.inl (Digits.nat_eq_not_zero_isnot_zero' h' h0)) (λ h' => Or.inr h')
    }
    | ⟨_, _⟩, ⟨_, true⟩, ⟨_, true⟩ => {
      simp[h] at *
      rw[h]
      simp[lt] at *
      exact Digits.nat.lt_of_lt_of_eq h1 h0.symm
    }
    | ⟨_, _⟩, ⟨_, false⟩, ⟨_, false⟩ => {
      simp[h] at *
      rw[h]
      simp[lt] at *
      exact Digits.nat.lt_of_eq_of_lt h0 h1
    }
  }
  | inr h => {
    have h0:x.digits.isZero ∧ y.digits.isZero:=by{
      apply notsame_sign_eq_to_zero
      exact h0
      exact h
    }
    match x, y, z with
    | ⟨_, _⟩, ⟨_, false⟩, ⟨_, true⟩ => contradiction
    | ⟨_, _⟩, ⟨_, true⟩, ⟨_, false⟩ => {
      simp[h] at *
      rw[h]
      simp[lt] at *
      rw[de_morgan_not_and] at *
      simp[h0.right] at h1
      exact Digits.nat.zero_lt_notzero h0.left h1
    }
    | ⟨_, _⟩, ⟨_, true⟩, ⟨_, true⟩ => {
      simp[h] at *
      rw[h]
      simp[lt] at *
      exact (Digits.nat.lt_not_zero h1) h0.right
    }
    | ⟨_, _⟩, ⟨_, false⟩, ⟨_, false⟩ => {
      simp[h] at *
      rw[h]
      simp[lt] at *
      rw[de_morgan_not_and] at *
      exact Or.inr (Digits.nat.lt_not_zero h1)
    }
  }
}

theorem lt_of_lt_of_eq{x y z:int}(h0:x < y)(h1:y =I z):x < z:=by{
  cases Decidable.em (y.negsign = z.negsign) with
  | inl h => {
    have h1:(y.digits) =N (z.digits):=by{
      apply same_sign_eq_to_nat_eq
      exact h1
      exact h
    }
    match x, y, z with
    | ⟨_, false⟩, ⟨_, true⟩, _ => contradiction
    | ⟨_, false⟩, ⟨_, false⟩, ⟨_, _⟩ => {
      simp[h] at *
      rw[←h]
      simp[lt] at *
      exact Digits.nat.lt_of_lt_of_eq h0 h1
    }
    | ⟨_, true⟩, ⟨_, true⟩, ⟨_, _⟩ => {
      simp[h] at *
      rw[←h]
      simp[lt] at *
      exact Digits.nat.lt_of_eq_of_lt h1.symm h0
    }
    | ⟨_, true⟩, ⟨_, false⟩, ⟨_, _⟩ => {
      simp[h] at *
      rw[←h]
      simp[lt] at *
      rw[de_morgan_not_and] at *
      exact h0.elim (λ h => Or.inl h) (λ h => Or.inr (Digits.nat_eq_not_zero_isnot_zero h h1))
    }
  }
  | inr h => {
    have h1:y.digits.isZero ∧ z.digits.isZero:=by{
      apply notsame_sign_eq_to_zero
      exact h1
      exact h
    }
    match z with
    | ⟨_, sign⟩ => {
      match x, y with
      | ⟨_, false⟩, ⟨_, true⟩ => contradiction
      | ⟨_, false⟩, ⟨_, false⟩ => {
        simp[h] at *
        have h:sign = true:=by match sign with | true => rfl | false => contradiction
        rw[h]
        simp[lt] at *
        exact (Digits.nat.lt_not_zero h0) h1.left
      }
      | ⟨_, true⟩, ⟨_, true⟩ => {
        simp[h] at *
        have h:sign = false:=by match sign with | false => rfl | true => contradiction
        rw[h]
        simp[lt] at *
        rw[de_morgan_not_and] at *
        exact Or.inl (Digits.nat.lt_not_zero h0)
      }
      | ⟨_, true⟩, ⟨_, false⟩ => {
        simp[h] at *
        have h:sign = true:=by match sign with | true => rfl | false => contradiction
        rw[h]
        simp[lt] at *
        rw[de_morgan_not_and] at *
        simp[h1.left] at h0
        exact Digits.nat.zero_lt_notzero h1.right h0
      }
    }
  }
}

theorem lt_of_le_of_lt{x y z:int}(h0:x ≤ y)(h1:y < z):x < z:=
  h0.elim (λ h0 => lt_of_eq_of_lt h0 h1) (λ h0 => h0.trans h1)

theorem lt_of_lt_of_le{x y z:int}(h0:x < y)(h1:y ≤ z):x < z:=
  h1.elim (λ h1 => lt_of_lt_of_eq h0 h1) (λ h1 => h0.trans h1)

theorem le_of_eq_of_le{x y z:int}(h0:x =I y)(h1:y ≤ z):x ≤ z:=
  h1.elim (λ h1 => (h0.trans h1).to_le) (λ h1 => (lt_of_eq_of_lt h0 h1 : x < z).to_le)

theorem le_of_le_of_eq{x y z:int}(h0:x ≤ y)(h1:y =I z):x ≤ z:=
  h0.elim (λ h0 => (h0.trans h1).to_le) (λ h0 => (lt_of_lt_of_eq h0 h1).to_le)

theorem le.trans{x y z:int}(h0:x ≤ y)(h1:y ≤ z):x ≤ z:=
  h0.elim (λ h0 => h1.elim (λ h1 => (h0.trans h1).to_le) (λ h1 => (lt_of_eq_of_lt h0 h1:x < z).to_le)) (λ h0 => h1.elim (λ h1 => (lt_of_lt_of_eq h0 h1).to_le) (λ h1 => (h0.trans h1).to_le))
end trans
end int
end wkmath
