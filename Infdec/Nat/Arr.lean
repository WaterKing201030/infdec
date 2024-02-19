import Infdec.Digits
import Infdec.Nat.Length

namespace wkmath
namespace digitsArr
def sum:digitsArr → Digits
  | δ => ε
  | a::d => a.sum + d
end digitsArr

namespace Digits
theorem cutTails_padtailzero_add_getTails_nat_eq(x y:Digits):(cutTails x y ++ y.toZero) + getTails x y =N x:=by{
  induction y generalizing x with
  | nil => {
    match x with | ε | _::_ => simp[cutTails, toZero, getTails, nat.eq.refl]
  }
  | cons y' yd ih => {
    match x with
    | ε => {
      simp[cutTails, getTails]
      exact zero_nat_eq_zero (toZero_isZero _) ε_isZero
    }
    | x'::xd => {
      match xd with | (0) | (1) | (2) => {
        rw[cutTails, toZero, getTails, append, add, add']
        simp[Digit.half_add3]
        simp[nat.eq]
        rw[←add]
        exact ih x'
      }
    }
  }
}

theorem padtailzero_le(x:Digits){y:Digits}(h:y.isZero):x ≤ x ++ y:=by{
  induction y with
  | nil => simp[nat.le.refl]
  | cons y' yd ih => {
    rw[isZero] at h
    rw[h.right]
    match x with
    | ε => exact nat.ε_le _
    | x'::xd => {
      rw[append]
      simp[nat.le]
      cases Decidable.em (x'.isZero) with
      | inl h' => {
        match xd with
        | (0) => {
          apply Or.inr
          simp
          apply zero_nat_eq_zero h'
          apply λ h'' => zero_append_zero_isZero h'' h.left
          simp[isZero]
          exact h'
        }
        | (1)
        | (2) => {
          apply Or.inl
          apply nat.zero_lt_notzero h'
          have ih:=ih h.left
          intro h''
          have ih:=nat.le_zero_isZero ih h''
          simp[isZero] at ih
        }
      }
      | inr h' => {
        apply Or.inl
        have ih:=ih h.left
        apply λ h => nat.lt_of_lt_of_le h ih
        exact nat.not_zero_lt_cons h' xd
      }
    }
  }
}

theorem not_zero_padtailzero_not_ε_lt{x y:Digits}(h0:¬x.isZero)(h1:y.isZero)(h2:y ≠ ε):x < x ++ y:=by{
  induction y generalizing x with
  | nil => contradiction
  | cons y' yd ih => {
    rw[isZero] at h1
    have ih:=ih h0 h1.left
    cases y' with
    | nil => simp[append]; exact nat.not_zero_lt_cons h0 _
    | cons y'' yd' => {
      simp[isZero] at *
      simp[h1.left.right, h1.right] at *
      apply ih.trans
      repeat rw[append]
      simp[nat.lt]
      apply nat.not_zero_lt_cons
      exact not_zero_append_isNotZero h0
    }
  }
}

theorem cutTails_add_getTails_le(x y:Digits):cutTails x y + getTails x y ≤ x:=by{
  have h:cutTails x y + getTails x y ≤ (cutTails x y ++ y.toZero) + getTails x y:=
    nat.le_of_add_left_le (padtailzero_le _ (toZero_isZero _)) _
  exact nat.le_of_le_of_eq h (cutTails_padtailzero_add_getTails_nat_eq _ _)
}

theorem cutTails_not_ε_not_zero_add_getTails_lt{x y:Digits}(h0:y ≠ ε)(h1:¬(cutTails x y).isZero):cutTails x y + getTails x y < x:=by{
  apply λ h => nat.lt_of_lt_of_eq h (cutTails_padtailzero_add_getTails_nat_eq x y)
  apply λ h => nat.lt_of_add_left_lt
  exact not_zero_padtailzero_not_ε_lt h1 (toZero_isZero y) (by{intro h; apply h0; match y with | ε => rfl | _::_ => rw[toZero] at h; contradiction})
}

theorem slice_sum_le(x:Digits){y:Digits}(h:y ≠ ε):(x.slice h).sum ≤ x:=by{
  rw[slice]
  cases Decidable.em (x ≤L y) with
  | inl h' => {
    simp[h']
    repeat rw[digitsArr.sum]
    rw[add.ε_add]
    exact nat.le.refl _
  }
  | inr h' => {
    simp[h']
    rw[digitsArr.sum]
    apply λ h => nat.le.trans h (cutTails_add_getTails_le x y)
    apply λ h => nat.le_of_add_left_le h (getTails x y)
    have : x.cutTails y <L x:=by{
      cases x with
      | nil => match y with | _::_ => simp[len.le] at h'
      | cons x' d' => {
        simp[cutTails, len.lt, len.le] at *
        match y with | _::_ => {
          simp[cutTails]
          exact len.lt_of_le_of_lt (cutTails_len_le _ _) (len.lt_cons x' d')
        }
      }
    }
    exact slice_sum_le _ h
  }
}
termination_by' {
  rel:=λ x y => x.fst <L y.fst
  wf:=InvImage.wf (λ x:(_:Digits) ×' _ => x.fst) len.lt.wf
}

theorem slice_cutTails_not_zero_sum_lt{x y:Digits}(h0:y ≠ ε)(h1:¬(cutTails x y).isZero):(x.slice h0).sum < x:=by{
  rw[slice]
  cases Decidable.em (x ≤L y) with
  | inl h => {
    rw[len_le_cutTails_eq_ε h] at h1
    contradiction
  }
  | inr h => {
    simp[h, digitsArr.sum]
    apply λ h => nat.lt_of_le_of_lt h (cutTails_not_ε_not_zero_add_getTails_lt h0 h1)
    apply nat.le_of_add_left_le
    exact slice_sum_le _ h0
  }
}
end Digits
end wkmath
