import Infdec.Nat.NatAddOrder

namespace wkmath
namespace Digits
def mul':Digits → Digit → Digit → Digits
  | ε, _, c => match c with
    | (0) => ε
    | (1) => ε::(1)
    | (2) => ε::(2)
  | xs::xd, d, c => (mul' xs d (Digit.mul_add3 xd d c).fst)::(Digit.mul_add3 xd d c).snd

theorem mul'.mul'_zero_carry_zero(x:Digits):mul' x (0) (0) = x.toZero:=by{
  induction x with
  | nil => simp
  | cons xs xd ih => {
    match xd with
    | (0) | (1) | (2) => simp[mul', Digit.mul_add3, toZero]; exact ih
  }
}

theorem mul'.mul'_one_carry_zero(x:Digits):mul' x (1) (0) = x:=by{
  induction x with
  | nil => simp
  | cons xs xd ih => {
    match xd with
    | (0) | (1) | (2) => simp[mul', Digit.mul_add3, ih]
  }
}

theorem mul'.mul'_zero_carry_zero_isZero(x:Digits):(mul' x (0) (0)).isZero:= by
  rw[mul'_zero_carry_zero]
  exact toZero_isZero _

theorem mul'.zero_mul'_carry_zero{x:Digits}(h:x.isZero)(d:Digit):mul' x d (0) = x:=by{
  induction x with
  | nil => match d with | (0) | (1) | (2) => simp
  | cons xs xd ih => {
    rw[isZero] at h
    simp[h.right] at *
    match d with | (0) | (1) | (2) => {
      simp[mul', Digit.mul_add3]
      exact ih h
    }
  }
}

theorem mul'.carry_eq_add''(x:Digits)(d c:Digit):mul' x d c =N add'' (mul' x d (0)) c:=by{
  induction x generalizing d c with
  | nil => {
    match c, d with
    | (0), (0)
    | (0), (1)
    | (0), (2)
    | (1), (0)
    | (1), (1)
    | (1), (2)
    | (2), (0)
    | (2), (1)
    | (2), (2) => simp[mul']
  }
  | cons xs xd ih => {
    match xd, c, d with
    | (0), (0), (0)
    | (0), (0), (1)
    | (0), (0), (2)
    | (0), (1), (0)
    | (0), (1), (1)
    | (0), (1), (2)
    | (0), (2), (0)
    | (0), (2), (1)
    | (0), (2), (2)
    | (1), (0), (0)
    | (1), (0), (1)
    | (1), (0), (2)
    | (1), (1), (0)
    | (1), (1), (1)
    | (1), (2), (0)
    | (2), (0), (0)
    | (2), (0), (1)
    | (2), (0), (2)
    | (2), (1), (0)
    | (2), (1), (2)
    | (2), (2), (0) => {
      simp[mul', Digit.mul_add3, add'', Digit.half_add3]
      exact nat.eq.refl _
    }
    | (1), (1), (2)
    | (1), (2), (1)
    | (1), (2), (2)
    | (2), (1), (1)
    | (2), (2), (1) => {
      simp[mul', Digit.mul_add3, add'', Digit.half_add3, nat.eq]
      exact ih _ _
    }
    | (2), (2), (2) => {
      simp[mul', Digit.mul_add3, add'', Digit.half_add3, nat.eq]
      apply (ih (2) (2)).trans
      rw[←add''.one_one_eq_two]
      apply nat.eq_of_eq_add''
      apply nat.eq.symm
      exact ih _ _
    }
  }
}

theorem mul'.carry_one_eq_add''_one(x:Digits)(d:Digit):mul' x d (1) = add'' (mul' x d (0)) (1) := by{
  induction x generalizing d with
  | nil => simp[mul', add'']
  | cons xs xd ih => {
    match xd, d with
    | (0), (0)
    | (0), (1)
    | (0), (2)
    | (1), (0)
    | (1), (1)
    | (2), (0)
    | (2), (2)  => {
      simp[mul', Digit.mul_add3, add'', Digit.half_add3]
    }
    | (1), (2)
    | (2), (1) => {
      simp[mul', Digit.mul_add3, add'', Digit.half_add3]
      exact ih _
    }
  }
}

theorem mul'.carry_eq_add(x:Digits)(d c:Digit):mul' x d c =N (mul' x d (0)) + ε::c:=
  (carry_eq_add'' x d c).trans (add_digit_nat_eq_add'' _ _).symm

theorem mul'.mul'_two_carry_zero(x:Digits):mul' x (2) (0) = x + x := by{
  induction x with
  | nil => simp
  | cons xs xd ih => {
    match xd with
    | (0)
    | (1) => {
      simp[mul', Digit.mul_add3, add, add', Digit.half_add3]
      exact ih
    }
    | (2) => {
      simp[mul', Digit.mul_add3, add, add', Digit.half_add3]
      rw[carry_one_eq_add''_one, ih, add]
      exact add''_add'_zero_one_eq_one _ _
    }
  }
}

def mul:Digits → Digits → Digits
  | _, ε => ε
  | x, ys::yd => (x.mul ys)::(0) + (x.mul' yd (0))

infixl:70 " * " => mul

theorem mul.mul_zero(x:Digits){y:Digits}(h:y.isZero):(x * y).isZero:=by{
  induction y with
  | nil => simp[mul]
  | cons ys yd ih => {
    rw[isZero] at h
    simp[h.right] at *
    rw[mul]
    rw[mul'.mul'_zero_carry_zero x]
    have h0:((x * ys)::(0)).isZero:=by simp[isZero]; exact ih h
    exact nat_eq_zero_isZero' (nat.add_zero (toZero_isZero x)) h0
  }
}

theorem mul.zero_mul{x:Digits}(h:x.isZero)(y:Digits):(x * y).isZero:=by{
  induction y with
  | nil => simp[mul]
  | cons ys yd ih => {
    rw[mul]
    rw[mul'.zero_mul'_carry_zero h]
    exact nat_eq_zero_isZero' (nat.add_zero h) (by simp[isZero]; exact ih)
  }
}

theorem mul.comm(x y:Digits):x * y =N y * x:=by{
  induction x generalizing y with
  | nil => exact zero_nat_eq_zero (zero_mul ε_isZero y) (mul_zero y ε_isZero)
  | cons xs xd ihx => {
    induction y generalizing xs xd with
    | nil => exact zero_nat_eq_zero (mul_zero _ ε_isZero) (zero_mul ε_isZero _)
    | cons ys yd ihy => {
      simp[mul,mul', Digit.mul_add3.comm, nat.eq]
      apply add_eq_to_add'_carry_eq
      apply (nat.eq_of_eq_add_eq (nat.eq.refl _) (mul'.carry_eq_add _ _ _)).trans
      apply nat.eq.symm
      apply (nat.eq_of_eq_add_eq (nat.eq.refl _) (mul'.carry_eq_add _ _ _)).trans
      repeat rw[←add.assoc]
      apply λ h => nat.eq_of_eq_add_eq h (nat.eq.refl _)
      apply (nat.eq_of_eq_add_eq (ihx (ys::yd)).symm (nat.eq.refl _)).trans
      rw[mul]
      rw[add.comm]
      rw[←add.assoc]
      apply λ h => nat.eq_of_eq_add_eq h (nat.eq.refl _)
      rw[add.comm]
      apply nat.eq.symm
      apply (ihy xs xd ihx).trans
      rw[mul]
      apply λ h => nat.eq_of_eq_add_eq h (nat.eq.refl _)
      simp[nat.eq]
      exact (ihx ys).symm
    }
  }
}

theorem mul.mul_cons_zero(x y:Digits):x * (y::(0)) =N (x * y)::(0):=by{
  rw[mul]
  exact nat.add_zero (mul'.mul'_zero_carry_zero_isZero x)
}

theorem mul.add''_one(x y:Digits):x * add'' y (1) =N x * y + x:=by{
  induction x generalizing y with
  | nil => simp; exact zero_nat_eq_zero (zero_mul ε_isZero _) (zero_mul ε_isZero _)
  | cons xs xd ih => {
    match y with
    | ε => simp[add'',mul,mul'.mul'_one_carry_zero]; exact nat.zero_add (by simp[isZero])
    | ys::yd => {
      match xd, yd with
      | (0), (0) => {
        simp[add, add', add'', Digit.half_add3, mul, mul', Digit.mul_add3, nat.eq]
        repeat rw[←add]
        simp[mul'.mul'_one_carry_zero]
        apply λ h => nat.eq_of_eq_add_eq h (nat.eq.refl _)
        exact (nat.add_zero (mul'.mul'_zero_carry_zero_isZero _)).symm
      }
      | (0), (1) => {
        simp[add, add', add'', Digit.half_add3, mul, mul', Digit.mul_add3, nat.eq]
        repeat rw[←add]
        simp[mul'.mul'_one_carry_zero, mul'.mul'_two_carry_zero]
        rw[add.assoc]
        exact nat.eq.refl _
      }
      | (0), (2) => {
        simp[add, add', add'', Digit.half_add3, mul, mul', Digit.mul_add3, nat.eq]
        repeat rw[←add]
        simp[mul'.mul'_two_carry_zero]
        apply (nat.add_zero (mul'.mul'_zero_carry_zero_isZero _)).trans
        apply (mul.comm (xs::(0)) _).trans
        simp[mul]
        apply (nat.add_zero (mul'.mul'_zero_carry_zero_isZero _)).trans
        have h:add'' ys (1) * xs :: (0) =N xs * add'' ys (1) :: (0) := by{
          simp[nat.eq]
          exact mul.comm _ _
        }
        apply h.trans
        apply (nat.cons_eq_of_eq (ih ys) (0)).trans
        rw[add_cons_zero_eq_cons_zero_add]
        apply (nat.eq_of_eq_add_eq (nat.eq.refl _) (cons_zero_nat_eq_triple xs)).trans
        rw[←add.assoc]
        repeat rw[add.assoc]
        apply λ h => nat.eq_of_eq_add_eq h (nat.eq.refl _)
        apply nat.eq.symm
        apply (mul.comm _ ys).trans
        apply (mul_cons_zero ys xs).trans
        simp[nat.eq]
        exact mul.comm _ _
      }
      | (1), (0) => {
        simp[add, add', add'', Digit.half_add3, mul, mul', Digit.mul_add3, nat.eq]
        repeat rw[←add]
        simp[mul'.mul'_one_carry_zero]
        apply λ h => nat.eq_of_eq_add_eq h (nat.eq.refl _)
        exact (nat.add_zero (mul'.mul'_zero_carry_zero_isZero _)).symm
      }
      | (1), (1) => {
        simp[add, add', add'', Digit.half_add3, mul, mul', Digit.mul_add3, nat.eq]
        repeat rw[←add]
        simp[mul'.mul'_one_carry_zero]
        rw[add.assoc]
        simp[mul'.mul'_two_carry_zero]
        apply λ h => nat.eq_of_eq_add_eq h (nat.eq.refl _)
        exact nat.eq.refl _
      }
      | (1), (2) => {
        simp[add, add', add'', Digit.half_add3, mul, mul', Digit.mul_add3, nat.eq]
        repeat rw[←add]
        apply (nat.add_zero (mul'.mul'_zero_carry_zero_isZero _)).trans
        apply (mul.comm _ _).trans
        simp[mul,mul'.mul'_one_carry_zero]
        rw[add.comm]
        rw[add]
        rw[add'_add''_carry_comm]
        apply add_eq_to_add'_carry_eq
        simp
        apply (nat.eq_of_eq_add_eq (nat.eq.refl ys) (nat.cons_eq_of_eq ((mul.comm _ _).trans (ih ys)) (0))).trans
        rw[add_cons_zero_eq_cons_zero_add]
        rw[mul'.mul'_two_carry_zero]
        rw[add.assoc]
        rw[←add.assoc]
        apply λ h => nat.eq_of_eq_add_eq h (cons_zero_nat_eq_triple xs)
        apply nat.eq.symm
        apply (mul.comm _ _).trans
        rw[mul, mul'.mul'_one_carry_zero]
        rw[add.comm]
        apply nat.eq_of_eq_add_eq (nat.eq.refl _)
        exact nat.cons_eq_of_eq (mul.comm _ _) (0)
      }
      | (2), (0) => {
        simp[add, add', add'', Digit.half_add3, mul, mul', Digit.mul_add3, nat.eq,mul'.mul'_one_carry_zero]
        repeat rw[←add]
        apply λ h => nat.eq_of_eq_add_eq h (nat.eq.refl _)
        exact (nat.add_zero (mul'.mul'_zero_carry_zero_isZero _)).symm
      }
      | (2), (1) => {
        simp[add, add', add'', Digit.half_add3, mul, mul', Digit.mul_add3, nat.eq,mul'.mul'_one_carry_zero, mul'.mul'_two_carry_zero]
        repeat rw[←add]
        rw[add.comm]
        apply (nat.eq_of_eq_add_eq (mul'.carry_eq_add'' _ _ _) (nat.eq.refl _)).trans
        rw[add,add'_add''_carry_comm]
        apply add_eq_to_add'_carry_eq
        rw[add.comm,add.assoc]
        apply nat.eq_of_eq_add_eq (nat.eq.refl _)
        simp
        rw[mul'.mul'_two_carry_zero]
        exact nat.eq.refl _
      }
      | (2), (2) => {
        simp[add, add', add'', Digit.half_add3, mul, mul', Digit.mul_add3, nat.eq,mul'.mul'_one_carry_zero, mul'.mul'_two_carry_zero]
        rw[←add]
        apply (nat.add_zero (mul'.mul'_zero_carry_zero_isZero xs)).trans
        rw[add'.carry_comm]
        rw[←add]
        apply (mul.comm _ _).trans
        rw[mul, mul'.mul'_two_carry_zero]
        rw[add,add]
        rw[add'.comm]
        rw[add'_add''_carry_comm]
        rw[add'.comm (add'' ys (0))]
        rw[add'_add''_one_one_eq_two]
        simp
        rw[add'.carry_comm]
        rw[add]
        apply nat.eq.symm
        apply (nat.eq_of_eq_add'_eq (nat.eq_of_eq_add'_eq (nat.eq.refl _) (mul'.carry_eq_add'' _ _ _)) (nat.eq.refl xs)).trans
        rw[add'.comm ((xs::(2))*ys)]
        rw[add'_add''_one_one_eq_two]
        rw[add'.carry_comm]
        apply add_eq_to_add'_carry_eq
        repeat rw[←add]
        rw[add.comm, ←add.assoc]
        rw[mul'.mul'_two_carry_zero]
        rw[add.comm xs]
        apply (nat.eq_of_eq_add_eq (cons_zero_nat_eq_triple xs).symm (nat.eq.refl _)).trans
        rw[add.comm]
        apply (nat.eq_of_eq_add_eq (mul.comm _ _) (nat.eq.refl _)).trans
        rw[mul,add.comm (ys * xs :: (0))]
        rw[mul'.mul'_two_carry_zero]
        rw[add.assoc]
        apply nat.eq_of_eq_add_eq (nat.eq.refl _)
        rw[←add_cons_zero_eq_cons_zero_add]
        apply nat.cons_eq_of_eq
        apply nat.eq.symm
        apply ((mul.comm _ _).trans (ih ys)).trans
        apply λ h => nat.eq_of_eq_add_eq h (nat.eq.refl _)
        exact mul.comm _ _
      }
    }
  }
}

theorem mul.right_distrib(x y z:Digits):x * (y + z) =N x * y + x * z:=by{
  match y, z with
  | _, ε => {
    simp
    exact (nat.add_zero (mul_zero x ε_isZero)).symm
  }
  | ε, _ => {
    simp
    exact (nat.zero_add (mul_zero x ε_isZero)).symm
  }
  | ys::yd, zs::zd => {
    have h:=right_distrib x ys zs
    match yd, zd with
    | (0), (0)
    | (0), (1)
    | (0), (2) => {
      simp[mul]
      simp[add,add', Digit.half_add3]
      repeat rw[←add]
      rw[←add.assoc]
      apply λ h => nat.eq_of_eq_add_eq h (nat.eq.refl _)
      rw[add.assoc]
      rw[add.comm ((x * ys)::(0))]
      apply nat.eq.symm
      rw[add.assoc]
      apply (nat.zero_add (mul'.mul'_zero_carry_zero_isZero x)).trans
      simp[add,add',Digit.half_add3,nat.eq]
      rw[←add,←add]
      rw[add.comm]
      apply nat.eq.symm
      exact h
    }
    | (1), (0)
    | (2), (0) => {
      simp[mul]
      simp[add,add', Digit.half_add3]
      repeat rw[←add]
      apply nat.eq.symm
      rw[add.comm, ←add.assoc]
      apply λ h => nat.eq_of_eq_add_eq h (nat.eq.refl _)
      rw[add.comm, ←add.assoc]
      apply (nat.add_zero (mul'.mul'_zero_carry_zero_isZero _)).trans
      simp[add,add',Digit.half_add3,nat.eq]
      repeat rw[←add]
      apply nat.eq.symm
      exact h
    }
    | (1), (1) => {
      simp[mul]
      simp[add,add', Digit.half_add3]
      repeat rw[←add]
      rw[←add.assoc]
      simp[mul'.mul'_two_carry_zero, mul'.mul'_one_carry_zero]
      rw[←add.assoc]
      apply λ h => nat.eq_of_eq_add_eq h (nat.eq.refl _)
      repeat rw[add.comm _ x]
      rw[add.assoc]
      apply nat.eq_of_eq_add_eq (nat.eq.refl _)
      simp[add,add',Digit.half_add3,nat.eq]
      repeat rw[←add]
      exact h
    }
    | (1), (2) => {
      simp[mul]
      simp[add,add', Digit.half_add3]
      repeat rw[←add]
      apply (nat.add_zero (mul'.mul'_zero_carry_zero_isZero _)).trans
      simp[mul'.mul'_two_carry_zero, mul'.mul'_one_carry_zero]
      rw[←add.assoc]
      rw[add.comm _ x]
      rw[add.comm]
      rw[←add.assoc, ←add.assoc]
      apply nat.eq.symm
      rw[add.assoc]
      apply (nat.eq_of_eq_add_eq (cons_zero_nat_eq_triple x).symm (nat.eq.refl _)).trans
      simp[add,add',Digit.half_add3]
      rw[←add,←add]
      simp[nat.eq]
      apply nat.eq.symm
      rw[←add''_add'_zero_one_eq_one]
      rw[←add]
      apply (mul.add''_one _ _).trans
      apply (nat.eq_of_eq_add_eq h (nat.eq.refl _)).trans
      rw[add.comm _ _]
      exact nat.eq.refl _
    }
    | (2), (1) => {
      simp[mul]
      simp[add,add', Digit.half_add3]
      repeat rw[←add]
      apply (nat.add_zero (mul'.mul'_zero_carry_zero_isZero _)).trans
      simp[mul'.mul'_two_carry_zero, mul'.mul'_one_carry_zero]
      rw[add.assoc]
      rw[add.comm (x + x)]
      rw[add.assoc]
      rw[←add.assoc x x x]
      apply nat.eq.symm
      apply (nat.eq_of_eq_add_eq (nat.eq.refl _) (nat.eq_of_eq_add_eq (nat.eq.refl _) (cons_zero_nat_eq_triple x).symm)).trans
      simp[add, add', Digit.half_add3, nat.eq]
      repeat rw[←add]
      rw[←add.assoc]
      apply nat.eq.symm
      rw[←add''_add'_zero_one_eq_one]
      rw[←add]
      apply (mul.add''_one _ _).trans
      exact nat.eq_of_eq_add_eq h (nat.eq.refl _)
    }
    | (2), (2) => {
      simp[mul]
      simp[add,add', Digit.half_add3]
      repeat rw[←add]
      rw[←add.assoc]
      simp[mul'.mul'_two_carry_zero, mul'.mul'_one_carry_zero]
      rw[←add.assoc]
      apply λ h => nat.eq_of_eq_add_eq h (nat.eq.refl _)
      rw[add.assoc, add.assoc]
      rw[add.comm (x + x)]
      rw[add.assoc]
      rw[←add.assoc x x x]
      apply nat.eq.symm
      apply (nat.eq_of_eq_add_eq (nat.eq.refl _) (nat.eq_of_eq_add_eq (nat.eq.refl _) (cons_zero_nat_eq_triple x).symm)).trans
      simp[add, add', Digit.half_add3, nat.eq]
      repeat rw[←add]
      rw[←add.assoc]
      apply nat.eq.symm
      rw[←add''_add'_zero_one_eq_one]
      rw[←add]
      apply (mul.add''_one _ _).trans
      exact nat.eq_of_eq_add_eq h (nat.eq.refl _)
    }
  }
}

theorem mul.left_distrib(x y z:Digits):(x + y) * z =N x * z + y * z :=
  ((comm (x+y) z).trans (right_distrib z x y)).trans (nat.eq_of_eq_add_eq (comm z x) (comm z y))

theorem mul.left_congr(x:Digits){y z:Digits}(h:y =N z):x * y =N x * z:=by{
  match y, z with
  | y, ε => exact zero_nat_eq_zero (mul_zero x (nat_eq_zero_isZero' h ε_isZero)) (mul_zero x ε_isZero)
  | ε, z => exact zero_nat_eq_zero (mul_zero x ε_isZero) (mul_zero x (nat_eq_zero_isZero h ε_isZero))
  | ys::yd, zs::zd => {
    simp[nat.eq] at h
    simp[h.right] at *
    rw[mul, mul]
    apply λ h => nat.eq_of_eq_add_eq h (nat.eq.refl _)
    simp[nat.eq]
    exact left_congr x h
  }
}

theorem mul.right_congr{x y:Digits}(h:x =N y)(z:Digits):x * z =N y * z:=
  ((mul.comm _ _).trans (left_congr z h)).trans (mul.comm _ _)

theorem mul.congr{x y z w:Digits}(h0:x =N y)(h1:z =N w):x * z =N y * w:=
  (left_congr x h1).trans (right_congr h0 w)

theorem mul.assoc(x y z:Digits): (x * y) * z =N x * (y * z):=by{
  match z with
  | ε => simp[mul]
  | zs::zd => {
    simp[mul]
    apply nat.eq.symm
    apply (right_distrib _ _ _).trans
    apply (nat.eq_of_eq_add_eq (mul_cons_zero _ _) (nat.eq.refl _)).trans
    apply nat.eq_of_eq_add_eq (nat.cons_eq_of_eq (assoc x y zs).symm (0))
    match zd with
    | (0) => exact zero_nat_eq_zero (mul_zero x (mul'.mul'_zero_carry_zero_isZero y)) (mul'.mul'_zero_carry_zero_isZero _)
    | (1) => simp[mul'.mul'_one_carry_zero]; exact nat.eq.refl _
    | (2) => simp[mul'.mul'_two_carry_zero]; exact right_distrib x y y
  }
}

def std_mul(x y:Digits):Digits:=
  (x * y).toStdNat

infixl:70 " *ₛ " => std_mul

theorem std_mul.closure{x y:Digits}(_:x.isStdNat)(_:y.isStdNat):(x *ₛ y).isStdNat:=
  toStdNat_isStdNat _

end Digits
end wkmath
