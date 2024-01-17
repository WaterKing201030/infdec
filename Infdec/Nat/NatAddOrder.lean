import Infdec.Nat.NatAdd

namespace wkmath
namespace Digits
section add''_properties
theorem nat.add''_not_zero_lt'(x:Digits){d:Digit}(h:d ≠ (0)):x < x.add'' d:=by{
  match x with
  | ε => match d with | (0) | (1) | (2) => simp at *
  | x'::xd => {
    match xd, d with
    | (0), (0)
    | (1), (0)
    | (2), (0) => contradiction
    | (0), (1)
    | (0), (2)
    | (1), (1) => {
      simp[add'', Digit.half_add3, nat.lt]
      exact Or.inr (nat.eq.refl _)
    }
    | (1), (2)
    | (2), (1)
    | (2), (2) => {
      simp[add'', Digit.half_add3, nat.lt]
      exact add''_not_zero_lt' _ (1).noConfusion
    }
  }
}

theorem nat.add''_le(x:Digits)(d:Digit):x ≤ x.add'' d:=by{
  match x with
  | ε => match d with | (0) | (1) | (2) => simp
  | x'::xd => {
    match xd, d with
    | (0), (0)
    | (0), (1)
    | (0), (2)
    | (1), (0)
    | (1), (1)
    | (2), (0) => {
      simp[add'', Digit.half_add3, nat.le]
      exact Or.inr (nat.eq.refl _)
    }
    | (1), (2)
    | (2), (1)
    | (2), (2) => {
      simp[add'', Digit.half_add3, nat.le]
      exact add''_not_zero_lt' _ (1).noConfusion
    }
  }
}

theorem nat.add''_le'(x:Digits)(d:Digit):ε::d ≤ x.add'' d:=by{
  match x with
  | ε => have h:=ε_add'' d; exact h.symm.to_le
  | x'::xd => match xd, d with
    | (0), (0)
    | (0), (1)
    | (0), (2)
    | (1), (0)
    | (1), (1)
    | (2), (0) => {
      simp[add'', Digit.half_add3]
      simp[nat.le]
      apply Or.comm
      rw[←nat.le_iff_eq_or_lt]
      exact nat.ε_le _
    }
    | (1), (2)
    | (2), (1)
    | (2), (2) => {
      simp[add'', Digit.half_add3]
      simp[nat.le]
      apply nat.ε_lt_notzero
      intro h
      have h':=add''_not_zero_lt' x' (1).noConfusion
      apply not_lt_zero x' h
      exact h'
    }
}

theorem nat.add''_not_zero_lt{x:Digits}(h:¬x.isZero)(d:Digit):ε::d < x.add'' d:=by{
  match x with
  | ε => contradiction
  | x'::xd => {
    simp[isZero] at h
    cases Decidable.em (x'.isZero) with
    | inl h' => {
      simp[h'] at h
      match xd,d with
      | (1), (0)
      | (1), (1)
      | (2), (0) => {
        simp[add'',Digit.half_add3,nat.lt]
        exact Or.inr (zero_nat_eq_zero ε_isZero h')
      }
      | (1), (2)
      | (2), (1)
      | (2), (2) => {
        simp[add'',Digit.half_add3,nat.lt]
        exact nat.ε_lt_notzero (nat.lt_not_zero (add''_not_zero_lt' x' (1).noConfusion))
      }
    }
    | inr h' => {
      match xd, d with
      | (0), (0)
      | (0), (1)
      | (0), (2) => {
        simp[add'',Digit.half_add3,nat.lt]
        exact nat.ε_lt_notzero h'
      }
      | (1), (0)
      | (1), (1)
      | (2), (0) => {
        simp[add'',Digit.half_add3,nat.lt]
        exact Or.inl (nat.ε_lt_notzero h')
      }
      | (1), (2)
      | (2), (1)
      | (2), (2) => {
        simp[add'',Digit.half_add3,nat.lt]
        exact nat.ε_lt_notzero (nat.lt_not_zero (add''_not_zero_lt' x' (1).noConfusion))
      }
    }
  }
}

theorem nat.lt_of_add''_lt(x:Digits){c d:Digit}(h:c < d):x.add'' c < x.add'' d :=by{
  match x with
  | ε => {
    exact nat.lt_of_eq_of_lt (ε_add'' c) (nat.lt_of_lt_of_eq (by{
      simp[lt]
      exact h
    }) (ε_add'' d).symm)
  }
  | x::xd => {
    match xd, c, d with
    | (0), (0), (1)
    | (1), (0), (1)
    | (0), (0), (2)
    | (0), (1), (2)
    | (2), (1), (2) => {
      simp[add'',Digit.half_add3,nat.lt]
      exact Or.inr (nat.eq.refl _)
    }
    | (2), (0), (1)
    | (1), (0), (2)
    | (2), (0), (2)
    | (1), (1), (2) => {
      simp[add'', Digit.half_add3, nat.lt]
      exact add''_not_zero_lt' x (1).noConfusion
    }
  }
}

theorem nat.le_of_add''_le(x:Digits){c d:Digit}(h:c ≤ d):x.add'' c ≤ x.add'' d:=by{
  rw[Digit.le_iff_eq_or_lt] at h
  cases h with
  | inl h => {
    rw[h]
    exact nat.le.refl _
  }
  | inr h => {
    apply nat.lt.to_le
    exact lt_of_add''_lt x h
  }
}

theorem nat.lt_to_add''_one_le{x y:Digits}(h:x < y):x.add'' (1) ≤ y:=by{
  match x, y with
  | ε, ε
  | _::_, ε => contradiction
  | ε, ys::yd => {
    simp[add'',nat.le]
    simp[nat.lt,isZero] at h
    cases Decidable.em (yd = (0)) with
    | inl h' => simp[h'] at h; exact Or.inl (nat.zero_lt_notzero ε_isZero h)
    | inr h' => {
      match yd with
      | (1)
      | (2) => simp; apply Or.comm; rw[←nat.le_iff_eq_or_lt]; exact nat.ε_le _
    }
  }
  | xs::xd, ys::yd => {
    match xd, yd with
    | (0), (0)
    | (0), (1)
    | (1), (0)
    | (1), (1) => {
      simp[add'', Digit.half_add3, nat.le]
      simp[nat.lt] at h
      exact h
    }
    | (2), (2) => {
      simp[add'', Digit.half_add3, nat.le]
      simp[nat.lt] at h
      apply Or.comm
      rw[←nat.le_iff_eq_or_lt]
      exact lt_to_add''_one_le h
    }
    | (2), (0)
    | (2), (1) => {
      simp[add'',Digit.half_add3,nat.le]
      simp[nat.lt] at h
      apply Or.comm
      rw[←nat.le_iff_eq_or_lt]
      exact lt_to_add''_one_le h
    }
    | (0), (2)
    | (1), (2) => {
      simp[add'',Digit.half_add3,nat.le]
      simp[nat.lt] at h
      exact h
    }
  }
}

theorem nat.lt_iff_add''_one_le{x y:Digits}:x < y ↔ x.add'' (1) ≤ y:=
  Iff.intro lt_to_add''_one_le (by{
    intro h'
    exact lt_of_lt_of_le (add''_not_zero_lt' x (1).noConfusion) h'
  })

theorem nat.lt_add''_one_to_le{x y:Digits}(h:x < y.add'' (1)):x ≤ y:=by{
  cases le_or_gt x y with
  | inl h' => exact h'
  | inr h' => {
    have h':=lt_to_add''_one_le h'
    have := lt_of_lt_of_le h h'
    simp[lt.irrefl] at this
  }
}

theorem nat.le_iff_lt_add''_one{x y:Digits}:x ≤ y ↔ x < y.add'' (1):=
  Iff.intro (by{
    intro h
    exact lt_of_le_of_lt h (add''_not_zero_lt' y (1).noConfusion)
  }) lt_add''_one_to_le

theorem nat.lt_of_lt_add''{x y:Digits}(h:x < y)(d:Digit):x.add'' d < y.add'' d:=by{
  match x, y with
  | ε, ε
  | _::_, ε => contradiction
  | ε, ys::yd => {
    match yd, d with
    | (0), (0) => simp[add'',Digit.half_add3,nat.lt]; exact nat.lt_not_zero h
    | (0), (1)
    | (0), (2) => {
      simp[add'',Digit.half_add3,nat.lt]
      simp[nat.lt] at h
      simp[isZero] at h
      exact nat.zero_lt_notzero ε_isZero h
    }
    | (1), (0)
    | (2), (0) => {
      simp[add'',Digit.half_add3,nat.lt]
      simp[isZero]
    }
    | (1), (1) => {
      simp[add'',Digit.half_add3,nat.lt]
      apply Or.comm
      rw[←nat.le_iff_eq_or_lt]
      exact nat.ε_le _
    }
    | (1), (2)
    | (2), (1)
    | (2), (2) => {
      simp[add'',Digit.half_add3,nat.lt]
      simp[nat.lt] at h
      exact nat.ε_lt_notzero (nat.lt_not_zero (add''_not_zero_lt' _ (1).noConfusion))
    }
  }
  | xs::xd, ys::yd => {
    simp[nat.lt] at h
    cases h with
    | inl h => {
      have h':=lt_of_lt_add'' h
      match xd, yd, d with
      | (0), (0), (0)
      | (0), (0), (1)
      | (0), (0), (2)
      | (1), (0), (0)
      | (1), (0), (1)
      | (1), (1), (0)
      | (1), (1), (1)
      | (2), (0), (0)
      | (2), (1), (0)
      | (2), (2), (0) => {
        simp[add'', Digit.half_add3, nat.lt]
        exact h
      }
      | (0), (1), (0)
      | (0), (1), (1)
      | (0), (2), (0)
      | (1), (2), (0) => {
        simp[add'', Digit.half_add3, nat.lt]
        exact Or.inl h
      }
      | (1), (1), (2)
      | (2), (1), (2)
      | (2), (2), (1)
      | (2), (2), (2) => {
        simp[add'', Digit.half_add3, nat.lt]
        exact h' _
      }
      | (1), (2), (2) => {
        simp[add'', Digit.half_add3, nat.lt]
        exact Or.inl (h' _)
      }
      | (0), (1), (2)
      | (0), (2), (1)
      | (0), (2), (2)
      | (1), (2), (1) => {
        simp[add'', Digit.half_add3, nat.lt]
        exact (add''_not_zero_lt' xs (1).noConfusion).trans (h' _)
      }
      | (1), (0), (2)
      | (2), (0), (1)
      | (2), (0), (2)
      | (2), (1), (1) => {
        simp[add'', Digit.half_add3, nat.lt]
        apply Or.comm
        rw[←nat.le_iff_eq_or_lt]
        exact lt_to_add''_one_le h
      }
    }
    | inr h => {
      match xd, yd, d with
      | (0), (1), (0)
      | (0), (1), (1)
      | (0), (2), (0)
      | (1), (2), (0) => {
        have h:=h.right
        simp[add'',Digit.half_add3]
        simp[nat.lt]
        exact Or.inr h
      }
      | (1), (2), (2) => {
        have h:=h.right
        simp[add'',Digit.half_add3]
        simp[nat.lt]
        exact Or.inr (eq_of_eq_add'' h _)
      }
      | (0), (1), (2)
      | (0), (2), (1)
      | (0), (2), (2)
      | (1), (2), (1) => {
        have h:=h.right
        simp[add'',Digit.half_add3]
        simp[nat.lt]
        exact nat.lt_of_eq_of_lt h (add''_not_zero_lt' ys (1).noConfusion)
      }
    }
  }
}

theorem nat.le_of_le_add''{x y:Digits}(h:x ≤ y)(d:Digit):x.add'' d ≤ y.add'' d:=by{
  cases h.to_eq_or_lt with
  | inl h => {
    exact (eq_of_eq_add'' h _).to_le
  }
  | inr h => {
    exact (lt_of_lt_add'' h _).to_le
  }
}

theorem nat.lt_of_lt_add''_lt{x y:Digits}{c d:Digit}(h0:x < y)(h1:c < d):x.add'' c < y.add'' d:=
  (lt_of_add''_lt x h1).trans (lt_of_lt_add'' h0 d)

theorem nat.lt_of_lt_add''_le{x y:Digits}{c d:Digit}(h0:x < y)(h1:c ≤ d):x.add'' c < y.add'' d:=by{
  cases h1.to_eq_or_lt with
  | inl h1 => rw[h1]; exact lt_of_lt_add'' h0 d
  | inr h1 => exact lt_of_lt_add''_lt h0 h1
}

theorem nat.lt_of_le_add''_lt{x y:Digits}{c d:Digit}(h0:x ≤ y)(h1:c < d):x.add'' c < y.add'' d:=by{
  cases h0.to_eq_or_lt with
  | inl h0 => exact nat.lt_of_eq_of_lt (eq_of_eq_add'' h0 c) (lt_of_add''_lt y h1)
  | inr h0 => exact lt_of_lt_add''_lt h0 h1
}

theorem nat.le_of_le_add''_le{x y:Digits}{c d:Digit}(h0:x ≤ y)(h1:c ≤ d):x.add'' c ≤ y.add'' d:=
  (le_of_add''_le x h1).trans (le_of_le_add'' h0 d)

theorem nat.lt_of_lt_of_add''_right_eq{x y:Digits}{d:Digit}(h0:x.add'' d < y.add'' d):x < y:=by{
  match d with
  | (0) => simp at h0; exact h0
  | (1) => {
    repeat rw[←le_iff_lt_add''_one, ←lt_iff_add''_one_le] at h0
    exact h0
  }
  | (2) => {
    repeat rw[←add''.one_one_eq_two] at h0
    repeat rw[←le_iff_lt_add''_one, ←lt_iff_add''_one_le] at h0
    exact h0
  }
}

theorem nat.lt_of_lt_of_add''_left_eq{x y:Digits}{c d:Digit}(h0:x.add'' c < y.add'' d)(h1:y =N x):c < d:=by{
  have h0:=lt_of_lt_of_eq h0 (eq_of_eq_add'' h1 d)
  cases Digit.le_or_gt d c with
  | inl h => {
    have h:=le_of_add''_le x h
    have h0:=lt_of_lt_of_le h0 h
    simp[lt.irrefl] at h0
  }
  | inr h => exact h
}

theorem nat.lt_of_lt_of_add''_right_gt{x y:Digits}{c d:Digit}(h0:x.add'' c < y.add'' d)(h1:d < c):x < y:=
  lt_of_lt_of_add''_right_eq ((lt_of_add''_lt x h1).trans h0)

theorem nat.lt_of_lt_of_add''_left_gt{x y:Digits}{c d:Digit}(h0:x.add'' c < y.add'' d)(h1:y < x):c < d:=
  lt_of_lt_of_add''_left_eq (h0.trans (lt_of_lt_add'' h1 d)) (eq.refl _)

theorem nat.lt_of_lt_of_add''_right_ge{x y:Digits}{c d:Digit}(h0:x.add'' c < y.add'' d)(h1:d ≤ c):x < y:=by{
  cases h1.to_eq_or_lt with
  | inl h1 => rw[h1] at h0; exact lt_of_lt_of_add''_right_eq h0
  | inr h1 => exact lt_of_lt_of_add''_right_gt h0 h1
}

theorem nat.lt_of_lt_of_add''_left_ge{x y:Digits}{c d:Digit}(h0:x.add'' c < y.add'' d)(h1:y ≤ x):c < d:=
  h1.to_eq_or_lt.elim (lt_of_lt_of_add''_left_eq h0) (lt_of_lt_of_add''_left_gt h0)

theorem nat.le_of_le_of_add''_right_ge{x y:Digits}{c d:Digit}(h0:x.add'' c ≤ y.add'' d)(h1:d ≤ c):x ≤ y:=by{
  rw[le_iff_not_gt]
  intro h
  exact lt.irrefl _ (lt_of_le_of_lt h0 (lt_of_lt_add''_le h h1))
}

theorem nat.le_of_le_of_add''_left_ge{x y:Digits}{c d:Digit}(h0:x.add'' c ≤ y.add'' d)(h1:y ≤ x):c ≤ d:=by{
  rw[Digit.le_iff_not_gt]
  intro h
  exact lt.irrefl _ (lt_of_le_of_lt h0 (lt_of_le_add''_lt h1 h))
}

theorem nat.lt_of_le_of_add''_right_gt{x y:Digits}{c d:Digit}(h0:x.add'' c ≤ y.add'' d)(h1:d < c):x < y:=by{
  rw[lt_iff_not_ge]
  intro h
  exact lt.irrefl _ (lt_of_le_of_lt h0 (lt_of_le_add''_lt h h1))
}

theorem nat.lt_of_le_of_add''_left_gt{x y:Digits}{c d:Digit}(h0:x.add'' c ≤ y.add'' d)(h1:y < x):c < d:=by{
  rw[Digit.lt_iff_not_ge]
  intro h
  exact lt.irrefl _ (lt_of_le_of_lt h0 (lt_of_lt_add''_le h1 h))
}
end add''_properties
section add'_properties
end add'_properties
section add_properties
end add_properties
end Digits
end wkmath
