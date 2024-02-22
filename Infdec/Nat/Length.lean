import Infdec.Nat.Peano

namespace wkmath
namespace Digits
def length:Digits → Digits
  | ε => ε
  | x::_ => x.length.Succ

theorem length_isStd(x:Digits):x.length.isStdNat:=by{
  induction x with
  | nil => {
    simp[length, isStdNat]
  }
  | cons x' _ ih => {
    rw[length]
    exact std_peano_2 ih
  }
}

theorem length_eq_of_len_eq{x y:Digits}(h:x =L y):x.length = y.length:=
  match x, y with
  | ε, ε => rfl
  | x'::_, y'::_ => by{
    simp[length]
    rw[len.eq] at h
    have h:=length_eq_of_len_eq h
    rw[h]
  }

theorem len_eq_of_length_eq{x y:Digits}(h:x.length = y.length):x =L y:=by{
  match x, y with
  | ε, ε => simp
  | x'::_, y'::_ => {
    simp[len.eq]
    simp[length] at h
    have h:=std_peano_3 (length_isStd x') (length_isStd y') h
    exact len_eq_of_length_eq h
  }
  | ε, ds::_
  | ds::_, ε => {
    simp[length] at h
    have h':=ε_lt_Succ ds.length
    rw[h] at h'
    exact ((nat.lt.irrefl _) h').elim
  }
}

theorem len_eq_iff_length_eq{x y:Digits}:x =L y ↔ x.length = y.length :=
  Iff.intro length_eq_of_len_eq len_eq_of_length_eq

theorem cons_length_eq_length_succ(x:Digits)(d:Digit):(x::d).length = x.length.Succ:=
  rfl

theorem append_length_eq_length_add(x y:Digits):(x ++ y).length = x.length + y.length := by{
  induction y with
  | nil => simp[length]
  | cons y' _ ih => {
    simp[length]
    rw[ih]
    exact (std_peano_add_2 (length_isStd x) (length_isStd y')).symm
  }
}

theorem nat.le_neg_one(x:Digits):x ≤ x.toNegOne:=by{
  induction x with
  | nil => simp
  | cons x' d ih => {
    simp[toNegOne, nat.le]
    cases ih.to_eq_or_lt with
    | inl ih => {
      apply Or.inr
      match d with
      | (0) | (1) | (2) => {
        simp
        exact ih
      }
    }
    | inr ih => {
      exact Or.inl ih
    }
  }
}
end Digits
end wkmath
