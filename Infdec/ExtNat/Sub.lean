import Infdec.Nat

namespace wkmath
namespace Digits
def sub(x y:Digits):Digits:=
  if x < y then ε else half_sub x y

infixl:65 " - " => sub

def std_sub(x y:Digits):Digits:=
  (x - y).toStdNat

infixl:65 " -ₛ " => std_sub

theorem nat.sub_add_cancel{x y:Digits}(h:y ≤ x):x - y + y =N x:=by{
  rw[sub]
  simp[h.to_not_gt]
  exact le_half_sub_add_cancel h
}

theorem nat.add_sub_cancel(x y:Digits):x + y - y =N x:=
  nat.add_right_cancel (sub_add_cancel (nat.add_left_le x y)) (nat.eq.refl y)

theorem nat.sub_le(x y:Digits):x - y ≤ x:=by{
  cases le_or_gt y x with
  | inl h => {
    exact add_left_le_of_le (le_of_eq_of_le (sub_add_cancel h) (add_right_le x y))
  }
  | inr h => {
    simp[sub,h]
    exact nat.ε_le _
  }
}

theorem sub_zero_eq{x y:Digits}(h:y.isZero):x - y = x:=by{
  simp[sub, (nat.zero_le x h).to_not_gt]
  rw[half_sub_zero _ h]
}

theorem nat.sub_zero_nat_eq(x:Digits){y:Digits}(h:y.isZero):x - y =N x:=by{
  rw[sub_zero_eq h]
  exact nat.eq.refl _
}

theorem nat.sub_not_zero_lt{x y:Digits}(hx:¬x.isZero)(hy:¬y.isZero):x - y < x:=by{
  cases le_or_gt y x with
  | inl h => {
    cases (sub_le x y).to_eq_or_lt with
    | inl h' => {
      have h':=eq_of_eq_add_eq h' (eq.refl y)
      have h':=(sub_add_cancel h).symm.trans h'
      exact ((add_right_not_zero_lt x hy).to_ne.elim h').elim
    }
    | inr h' => exact h'
  }
  | inr h => {
    simp[sub,h]
    exact nat.ε_lt_notzero hx
  }
}

theorem nat.nat_eq_sub_zero{x y:Digits}(h:x =N y):(x - y).isZero:=by{
  have h:x - y + y =N ε + y:=by{
    rw[add.ε_add]
    exact (sub_add_cancel h.symm.to_le).trans h
  }
  have h:=add_right_cancel h (eq.refl y)
  exact nat_eq_zero_isZero' h ε_isZero
}

theorem nat.sub_add_eq_sub_sub(x y z:Digits):x - (y + z) =N x - y - z:=by{
  cases le_or_gt (y + z) x with
  | inl h => {
    have h0:x - (y + z) + (y + z) =N x:=sub_add_cancel h
    have h1:x - y - z + (y + z) =N x:=by{
      rw[add.comm y, ←add.assoc]
      have h1:y ≤ x:=(add_right_le y z).trans h
      have h2:z ≤ x - y:=by{
        rw[add.comm] at h
        exact add_left_le_of_le (le_of_le_of_eq h (sub_add_cancel h1).symm)
      }
      apply (eq_of_eq_add_eq (sub_add_cancel h2) (eq.refl y)).trans
      exact sub_add_cancel h1
    }
    have h2:=h0.trans h1.symm
    exact add_right_cancel h2 (eq.refl (y + z))
  }
  | inr h => {
    rw[sub]
    simp[h]
    have h:x - y ≤ z:=by{
      cases le_or_gt y x with
      | inl h' => {
        rw[add.comm] at h
        exact (add_left_lt_of_lt (lt_of_eq_of_lt (sub_add_cancel h') h)).to_le
      }
      | inr h => {
        rw[sub]
        simp[h]
        exact ε_le z
      }
    }
    rw[le_iff_eq_or_lt] at h
    cases h with
    | inl h => {
      have h:=nat_eq_sub_zero h
      exact zero_nat_eq_zero ε_isZero h
    }
    | inr h => {
      rw[sub]
      simp[h]
    }
  }
}

theorem nat.sub_comm(x y z:Digits):x - y - z =N x - z - y:=by{
  apply (sub_add_eq_sub_sub x y z).symm.trans
  rw[add.comm]
  exact sub_add_eq_sub_sub x z y
}

theorem nat.add_sub_comm{x y:Digits}(h:y ≤ x)(z:Digits):x - y + z =N x + z - y:=by{
  have h':=h.trans (add_right_le x z)
  have h'':x - y + z + y =N x + z - y + y:=by{
    rw[add.assoc, add.comm z, ←add.assoc]
    apply λ h => eq.trans h (sub_add_cancel h').symm
    apply λ h => eq_of_eq_add_eq h (eq.refl z)
    exact sub_add_cancel h
  }
  exact add_right_cancel h'' (eq.refl _)
}

theorem nat.add_sub_assoc(x:Digits){y z:Digits}(h:z ≤ y):x + y - z =N x + (y - z):=by{
  have h':x + y - z + z =N x + (y - z) + z:=by{
    have h':z ≤ x + y:=h.trans (add_left_le x y)
    rw[add.assoc _ (y - z)]
    exact (sub_add_cancel h').trans (eq_of_eq_add_eq (eq.refl x) (sub_add_cancel h)).symm
  }
  exact add_right_cancel h' (eq.refl z)
}

theorem nat.eq_of_eq_sub_eq{x y z w:Digits}(h0:x =N z)(h1:y =N w):x - y =N z - w:=by{
  cases Decidable.em (x < y) with
  | inl h => {
    have h':=lt_of_lt_of_eq (lt_of_eq_of_lt h0.symm h) h1
    rw[sub, sub]
    simp[h, h']
  }
  | inr h => {
    have h:=le_of_not_gt h
    have h':=le_of_le_of_eq (le_of_eq_of_le h1.symm h) h0
    have h'':x - y + y =N z - w + w:=((sub_add_cancel h).trans h0).trans (sub_add_cancel h').symm
    exact add_right_cancel h'' h1
  }
}

theorem nat.sub_sub_eq_sub_add{x y z:Digits}(h0:y ≤ x + z)(h1:z ≤ y):x - (y - z) =N x + z - y:=by{
  have h2:y - z ≤ x:=add_left_le_of_le (le_of_eq_of_le (sub_add_cancel h1) h0)
  have h3:x - (y - z) + (y - z) =N x + z - y + (y - z):=by{
    apply (sub_add_cancel h2).trans
    apply eq.symm
    apply (add_sub_assoc _ h1).symm.trans
    have h3:x + z - y + y =N x + z:=sub_add_cancel h0
    exact (eq_of_eq_sub_eq h3 (eq.refl _)).trans (add_sub_cancel x z)
  }
  exact add_right_cancel h3 (eq.refl _)
}

end Digits
end wkmath
