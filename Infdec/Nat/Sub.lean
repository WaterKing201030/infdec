import Infdec.Nat.NatAddOrder

namespace wkmath
namespace Digits

def half_sub':Digits → Digits → Digit → Digits
  | ε, _, _ => ε
  | xs::xd, ε, d => (half_sub' xs ε (xd.half_sub3 (0) d).fst)::(xd.half_sub3 (0) d).snd
  | xs::xd, ys::yd, d => (half_sub' xs ys (xd.half_sub3 yd d).fst)::(xd.half_sub3 yd d).snd

def half_sub(x y:Digits):=
  half_sub' x y (0)

theorem half_sub_zero(x:Digits){y:Digits}(h:y.isZero):half_sub x y = x:=by{
  match x, y with
  | ε, ε => simp
  | ε, _::_ => simp[half_sub,half_sub']
  | xs::xd, ε => {
    rw[half_sub]
    match xd with
    | (0)
    | (1)
    | (2) => simp[half_sub, half_sub', Digit.half_sub3]; rw[←half_sub]; exact half_sub_zero xs ε_isZero
  }
  | xs::xd, ys::yd => {
    rw[isZero] at h
    rw[h.right]
    match xd with
    | (0)
    | (1)
    | (2) => simp[half_sub, half_sub', Digit.half_sub3]; rw[←half_sub]; exact half_sub_zero xs h.left
  }
}

theorem inductionOn₂
  {P:Digits → Digits → Prop}
  (left:∀(x:Digits), P x ε)
  (right:∀(y:Digits), P ε y)
  (cons:∀(x y:Digits)(c d:Digit), P x y → P (x::c) (y::d))
  (x y:Digits): P x y := by{
    match x, y with
    | x, ε => exact left x
    | ε, y => exact right y
    | x::c, y::d => {
      apply cons x y c d
      exact inductionOn₂ left right cons x y
    }
  }

theorem lt_half_sub'_add'_carry_one_cancel{x y:Digits}(h:y<x):add' (half_sub' x y (1)) y (1) =N x:=by{
  induction x, y using inductionOn₂ with
  | left x => {
    induction x with
    | nil => contradiction
    | cons xs xd ih => {
      have h:=nat.lt_not_zero h
      match xd with
      | (0) => {
        simp[isZero] at h
        have h:=nat.ε_lt_notzero h
        simp[half_sub', Digit.half_sub3]
        simp[add'', Digit.half_add3, nat.eq]
        simp at ih
        exact ih h
      }
      | (1)
      | (2) => {
        simp[half_sub', Digit.half_sub3]
        simp[add'', Digit.half_add3, nat.eq]
        rw[←half_sub]
        rw[half_sub_zero xs ε_isZero]
        exact nat.eq.refl _
      }
    }
  }
  | right y => {
    simp[nat.not_lt_ε] at h
  }
  | cons xs ys xd yd ih => {
    match xd, yd with
    | (0), (0)
    | (0), (1)
    | (0), (2)
    | (1), (1)
    | (1), (2)
    | (2), (2) => {
      simp[half_sub', Digit.half_sub3]
      simp[nat.lt] at h
      simp[add, add', Digit.half_add3, nat.eq]
      exact ih h
    }
    | (1), (0)
    | (2), (0)
    | (2), (1) => {
      simp[half_sub', Digit.half_sub3]
      simp[nat.lt] at h
      simp[add, add', Digit.half_add3, nat.eq]
      have h:=nat.le_iff_eq_or_lt.mpr h.comm
      rw[←half_sub, ←add]
      induction xs, ys using inductionOn₂ with
      | left xs => {
        simp[half_sub_zero _ ε_isZero]
        exact nat.eq.refl _
      }
      | right ys => {
        have h':=nat.le_ε_isZero h
        simp[half_sub_zero _ h']
        exact zero_nat_eq_zero h' ε_isZero
      }
      | cons xs ys xd yd ih' => {
        match xd, yd with
        | (0), (0)
        | (1), (1)
        | (2), (2) => {
          simp[half_sub, half_sub', Digit.half_sub3] at *
          simp[nat.le] at h
          simp[add, add', Digit.half_add3, nat.eq] at *
          simp[nat.lt] at ih
          exact ih' ih h (nat.le_iff_eq_or_lt.mpr h.comm)
        }
        | (1), (0)
        | (2), (0)
        | (2), (1)
        | (0), (1)
        | (0), (2)
        | (1), (2) => {
          simp[half_sub, half_sub', Digit.half_sub3] at *
          simp[nat.le] at h
          simp[add, add', Digit.half_add3, nat.eq] at *
          simp[nat.lt] at ih
          exact ih h
        }
      }
    }
  }
}

theorem le_half_sub_add_cancel{x y:Digits}(h:y ≤ x):(half_sub x y)+y=N x:=by{
  match y with
  | ε => rw[half_sub_zero _ ε_isZero]; simp; exact nat.eq.refl x
  | ys::yd => {
    match x with
    | ε => {
      have h:=nat.le_ε_isZero h
      simp[half_sub,half_sub']
      exact zero_nat_eq_zero h ε_isZero
    }
    | xs::xd => {
      rw[half_sub]
      match xd, yd with
      | (0), (0)
      | (1), (0)
      | (1), (1)
      | (2), (0)
      | (2), (1)
      | (2), (2) => {
        simp[half_sub', Digit.half_sub3]
        simp[nat.le] at h
        simp[add, add', Digit.half_add3, nat.eq]
        rw[←half_sub, ←add]
        have h:=h.comm
        rw[←nat.le_iff_eq_or_lt] at h
        exact le_half_sub_add_cancel h
      }
      | (0), (1)
      | (0), (2)
      | (1), (2) => {
        simp[half_sub', Digit.half_sub3]
        simp[nat.le] at h
        simp[add, add', Digit.half_add3, nat.eq]
        exact lt_half_sub'_add'_carry_one_cancel h
      }
    }
  }
}

end Digits
end wkmath
