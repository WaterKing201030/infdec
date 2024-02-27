import Infdec.Cycdec.Base

namespace wkmath

namespace Digits
theorem One_toNat_eq_1:One.toNat = 1:=by simp
theorem one_pad_zero_not_zero(x:Digits):¬(ε::(1) ++ x.toOneBaseNat).isZero:=by{
  intro h
  induction x with
  | nil => simp[toOneBaseNat] at h
  | cons _ d ih => {
    match d with
    | (0)
    | (1)
    | (2) => {
      simp[toOneBaseNat, append, isZero] at h
      simp[triple, double] at h
      repeat rw[←append.assoc] at h
      rw[append.assoc (ε :: (1) ++ toOneBaseNat _)] at h
      exact not_zero_append_isNotZero ih h
    }
  }
}
end Digits

structure Frac where
  num: Nat
  den: Nat
  inv: den ≠ 0

namespace Frac
def eq(x y:Frac):=
  x.den * y.num = x.num * y.den
notation:50 lhs:51 " =F " rhs:51 => eq lhs rhs

theorem eq.refl(x:Frac):x =F x:=
  match x with | ⟨_, _, _⟩ => Nat.mul_comm _ _

theorem eq.symm{x y:Frac}(h:x =F y):y =F x:=by{
  match x, y with
  | ⟨_, _, _⟩, ⟨_, _, _⟩ => {
    simp[eq] at *
    exact ((Nat.mul_comm _ _).trans h.symm).trans (Nat.mul_comm _ _)
  }
}

theorem eq.trans{x y z:Frac}(h0:x =F y)(h1:y =F z):x =F z:=by{
  match x, y, z with
  | ⟨x0, x1, hx⟩, ⟨y0, y1, hy⟩, ⟨z0, z1, hz⟩ => {
    simp[eq] at *
    apply Nat.eq_of_mul_eq_mul_right (Nat.ne_zero_iff_gt_zero.mp hy)
    rw[Nat.mul_assoc]
    rw[Nat.mul_comm z0]
    rw[h1]
    rw[←Nat.mul_assoc]
    rw[h0]
    rw[Nat.mul_assoc]
    rw[Nat.mul_comm y1]
    rw[←Nat.mul_assoc]
  }
}

theorem eq_mod_cancel(x:Nat){y z:Nat}(hy:y ≠ 0)(hz:z ≠ 0):⟨x * z, y * z, Nat.mul_ne_zero hy hz⟩ =F ⟨x,y,hy⟩:=by{
  simp[eq]
  rw[Nat.mul_comm y z]
  rw[Nat.mul_comm _ _]
  exact (Nat.mul_assoc _ _ _).symm
}

def mul(x y:Frac):Frac:=
  ⟨x.num * y.num, x.den * y.den, Nat.mul_ne_zero x.inv y.inv⟩

infixl:70 " * " => mul

def ofNat(x:Nat):Frac:=
  ⟨x, 1, Nat.noConfusion⟩
end Frac

namespace cyc
-- 感觉不管怎么写都会比较复杂
def toFrac(x:cyc):Frac:=
  if x.exp.negsign then
    ⟨(x.pre * x.post.toNegOne + x.post).toNat, (x.post.toNegOne ++ x.exp.digits.toOneBaseNat).toNat, λ h => Digits.not_zero_append_isNotZero (Digits.not_ε_toNegOne_not_zero x.inv) (Digits.isZero_iff_toNat_eq_zero.mpr h)
    ⟩
  else
    ⟨((x.pre * x.post.toNegOne + x.post) ++ x.exp.digits.toOneBaseNat).toNat, x.post.toNegOne.toNat, λ h => Digits.not_ε_toNegOne_not_zero x.inv (Digits.isZero_iff_toNat_eq_zero.mpr h)⟩

def fraceq(x y:cyc):=
  x.toFrac =F y.toFrac

notation:50 lhs:51 " =F " rhs:51 => fraceq lhs rhs

theorem fraceq.refl(x:cyc):x =F x:=by{
  rw[fraceq]
  exact Frac.eq.refl _
}

theorem fraceq.symm{x y:cyc}(h:x =F y):y =F x:=by{
  rw[fraceq] at *
  exact h.symm
}

theorem fraceq.trans{x y z:cyc}(h0:x =F y)(h1:y =F z):x =F z:=by{
  rw[fraceq] at *
  exact h0.trans h1
}

theorem toStdNat_fraceq(n:Digits){x:Digits}(e:int)(h:x ≠ ε):⟨n, x, e, h⟩ =F ⟨n.toStdNat, x, e, h⟩:=by{
  rw[fraceq]
  match e with
  | ⟨i, true⟩ => {
    simp[toFrac]
    rw[Digits.add_toNat_eq_toNat_add]
    rw[Digits.add_toNat_eq_toNat_add]
    simp[Frac.eq]
    simp[Nat.mul_add, Nat.add_mul]
    simp[Digits.mul_toNat_eq_toNat_mul]
    apply λ{a b c d:Nat}(h0:a = b)(h1:c = d) => ((by simp[h0, h1]):a + c = b + d)
    . {
      rw[Nat.mul_comm]
      apply congrArg (λ y => y * (x.toNegOne ++ i.toOneBaseNat).toNat)
      apply congrArg (λ y => y * x.toNegOne.toNat)
      rw[←Digits.nat_eq_iff_toNat_eq]
      exact Digits.toStdNat_nat_eq _
    }
    . rw[Nat.mul_comm]
  }
  | ⟨i, false⟩ => {
    simp[toFrac, Frac.eq]
    rw[Nat.mul_comm]
    apply congrArg (λ y => y * x.toNegOne.toNat)
    rw[←Digits.nat_eq_iff_toNat_eq]
    apply (Digits.padtailzero_nat_eq_mul_one_pad_zero _ (Digits.toOneBaseNat_isZero _)).trans
    apply Digits.nat.eq.symm
    apply (Digits.padtailzero_nat_eq_mul_one_pad_zero _ (Digits.toOneBaseNat_isZero _)).trans
    rw[Digits.nat_eq_iff_toNat_eq]
    rw[Digits.mul_toNat_eq_toNat_mul]
    rw[Digits.mul_toNat_eq_toNat_mul]
    apply congrArg (λ y => y * (ε::(1) ++ i.toOneBaseNat).toNat)
    rw[Digits.add_toNat_eq_toNat_add]
    rw[Digits.add_toNat_eq_toNat_add]
    apply congrArg (λ y => y + x.toNat)
    rw[Digits.mul_toNat_eq_toNat_mul]
    rw[Digits.mul_toNat_eq_toNat_mul]
    apply congrArg (λ y => y * x.toNegOne.toNat)
    rw[←Digits.nat_eq_iff_toNat_eq]
    exact (Digits.toStdNat_nat_eq _).symm
  }
}

theorem minCyc_fraceq(n:Digits){x:Digits}(e:int)(h:x ≠ ε):⟨n, x, e, h⟩ =F ⟨n, x.minCyc, e, Digits.not_ε_minCyc_not_ε h⟩:=by{
  rw[fraceq]
  match e with
  | ⟨i, true⟩ => {
    simp[toFrac, Frac.eq]
    rw[Digits.nat_eq_iff_toNat_eq.mp (Digits.padtailzero_nat_eq_mul_one_pad_zero _ (Digits.toOneBaseNat_isZero _))]
    rw[Digits.nat_eq_iff_toNat_eq.mp (Digits.padtailzero_nat_eq_mul_one_pad_zero _ (Digits.toOneBaseNat_isZero _))]
    rw[Digits.mul_toNat_eq_toNat_mul]
    rw[Digits.mul_toNat_eq_toNat_mul]
    rw[Nat.mul_assoc]
    rw[Nat.mul_comm ((ε::(1) ++ i.toOneBaseNat).toNat)]
    rw[←Nat.mul_assoc, ←Nat.mul_assoc]
    apply congrArg (λ y => y * (ε::(1) ++ i.toOneBaseNat).toNat)
    rw[←Digits.mul_toNat_eq_toNat_mul]
    rw[←Digits.mul_toNat_eq_toNat_mul]
    rw[←Digits.nat_eq_iff_toNat_eq]
    have ⟨y,hy0, _⟩:=Digits.isCycParent_exists_replace (Digits.isCycParent_minCyc x)
    have hy2:=Digits.replace_eq_mul_one_zero_cycle y x.minCyc
    rw[hy0] at hy2
    apply (Digits.mul.right_distrib _ _ _).trans
    apply Digits.nat.eq.symm
    apply (Digits.mul.left_distrib _ _ _).trans
    apply Digits.nat.eq_of_eq_add_eq
    . {
      apply (Digits.mul.right_congr (Digits.mul.comm n _) _).trans
      apply (Digits.mul.assoc _ _ _).trans
      exact Digits.nat.eq.refl _
    }
    . {
      apply (Digits.mul.right_congr hy2 _).trans
      apply (Digits.mul.assoc _ _ _).trans
      apply (Digits.mul.comm _ _).trans
      apply Digits.mul.right_congr
      rw[←Digits.toNegOne_toZero_eq_toZero]
      have h0:=Digits.replace_eq_mul_one_zero_cycle y x.minCyc.toNegOne
      apply (Digits.mul.comm _ _).trans
      apply h0.symm.trans
      rw[Digits.replace_toNegOne_comm]
      rw[hy0]
      exact Digits.nat.eq.refl _
    }
  }
  | ⟨i, false⟩ => {
    simp[toFrac, Frac.eq]
    rw[Digits.nat_eq_iff_toNat_eq.mp (Digits.padtailzero_nat_eq_mul_one_pad_zero _ (Digits.toOneBaseNat_isZero _))]
    rw[Digits.nat_eq_iff_toNat_eq.mp (Digits.padtailzero_nat_eq_mul_one_pad_zero _ (Digits.toOneBaseNat_isZero _))]
    rw[Digits.mul_toNat_eq_toNat_mul]
    rw[Digits.mul_toNat_eq_toNat_mul]
    rw[←Nat.mul_assoc]
    apply Eq.symm
    rw[Nat.mul_assoc]
    rw[Nat.mul_comm (ε::(1) ++ i.toOneBaseNat).toNat]
    rw[←Nat.mul_assoc]
    apply congrArg (λ y => y * (ε::(1) ++ i.toOneBaseNat).toNat)
    rw[←Digits.mul_toNat_eq_toNat_mul]
    rw[←Digits.mul_toNat_eq_toNat_mul]
    rw[←Digits.nat_eq_iff_toNat_eq]
    have ⟨y,hy0, _⟩:=Digits.isCycParent_exists_replace (Digits.isCycParent_minCyc x)
    have hy2:=Digits.replace_eq_mul_one_zero_cycle y x.minCyc
    rw[hy0] at hy2
    apply (Digits.mul.left_distrib _ _ _).trans
    apply Digits.nat.eq.symm
    apply (Digits.mul.right_distrib _ _ _).trans
    apply Digits.nat.eq_of_eq_add_eq
    . {
      apply Digits.nat.eq.symm
      apply (Digits.mul.right_congr (Digits.mul.comm n _) _).trans
      apply (Digits.mul.assoc _ _ _).trans
      exact Digits.nat.eq.refl _
    }
    . {
      apply Digits.nat.eq.symm
      apply (Digits.mul.right_congr hy2 _).trans
      apply (Digits.mul.assoc _ _ _).trans
      apply (Digits.mul.comm _ _).trans
      apply Digits.mul.right_congr
      rw[←Digits.toNegOne_toZero_eq_toZero]
      have h0:=Digits.replace_eq_mul_one_zero_cycle y x.minCyc.toNegOne
      apply (Digits.mul.comm _ _).trans
      apply h0.symm.trans
      rw[Digits.replace_toNegOne_comm]
      rw[hy0]
      exact Digits.nat.eq.refl _
    }
  }
}

theorem toStdInt_fraceq(n:Digits){x:Digits}(e:int)(h:x ≠ ε):⟨n, x, e, h⟩ =F ⟨n, x, e.toStdInt, h⟩:=by{
  match e with
  | ⟨i, true⟩
  | ⟨i, false⟩ => {
    simp[int.toStdInt]
    cases Decidable.em (i.isZero) with
    | inl h' => {
      simp[h']
      simp[fraceq, toFrac, Frac.eq, Digits.toOneBaseNat]
      rw[Digits.zero_toOneBaseNat_is_ε h', Digits.append]
      exact Nat.mul_comm _ _
    }
    | inr h' => {
      simp[h']
      simp[fraceq, toFrac, Frac.eq]
      have h'':i.toStdNat.toOneBaseNat = i.toOneBaseNat:=Digits.toOneBaseNat_eq_of_nat_eq (Digits.toStdNat_nat_eq i)
      rw[h'']
      exact Nat.mul_comm _ _
    }
  }
}

theorem pre_nat_eq_fraceq{m n x:Digits}(h:x ≠ ε){e:int}(he:m =N n):⟨m, x, e, h⟩ =F ⟨n, x, e, h⟩:=by{
  apply λ h' => ((toStdNat_fraceq m e h).trans h').trans (toStdNat_fraceq n e h).symm
  have h'':=Digits.nat_eq_iff_toStdNat_eq.mp he
  rw[h'']
  exact fraceq.refl _
}

theorem exp_int_eq_fraceq(n:Digits){x:Digits}(h:x ≠ ε){i j:int}(he:i =I j):⟨n, x, i, h⟩ =F ⟨n, x, j, h⟩:=by{
  apply λ h' => ((toStdInt_fraceq n i h).trans h').trans (toStdInt_fraceq n j h).symm
  have h'':=int.eq_iff_toStdInt_eq.mp he
  rw[h'']
  exact fraceq.refl _
}

theorem exp_add_one_toFrac_eq_num_mul_3(n:Digits){x:Digits}(e:int)(h:x≠ε):(⟨n,x,e + int.One,h⟩:cyc).toFrac =F ⟨(⟨n, x, e, h⟩:cyc).toFrac.num * 3, (⟨n, x, e, h⟩:cyc).toFrac.den, (⟨n, x, e, h⟩:cyc).toFrac.inv⟩:=by{
  match e with
  | ⟨i, true⟩ => {
    simp[int.add, int.One]
    cases Decidable.em (ε::(1) ≤ i) with
    | inl h' => {
      simp[h']
      simp[toFrac, Frac.eq]
      have h'':i =N (i - ε::(1)).Succ:=by{
        rw[Digits.Succ, Digits.One]
        exact (Digits.nat.sub_add_cancel h').symm
      }
      rw[Digits.toOneBaseNat_eq_of_nat_eq h'']
      rw[Digits.Succ_toOneBaseNat_eq_toOneBaseNat_cons_zero]
      rw[Digits.append]
      rw[Digits.toNat]
      simp[Digit.toNat]
      rw[Nat.mul_left_comm]
    }
    | inr h' => {
      simp[h']
      simp[toFrac, Frac.eq]
      rw[←Digits.nat.lt_iff_not_ge] at h'
      rw[←Digits.One] at h'
      rw[←Digits.isZero_iff_lt_One] at h'
      simp[Digits.sub_zero_eq h', Digits.zero_toOneBaseNat_is_ε h']
      simp[Digits.toOneBaseNat, Digits.append, Digits.toNat, Digit.toNat]
      exact Nat.mul_comm _ _
    }
  }
  | ⟨i, false⟩ => {
    simp[int.add, int.One]
    simp[toFrac, Frac.eq]
    rw[Nat.mul_comm]
    apply congrArg (λ y => y * x.toNegOne.toNat)
    rw[←Digits.One, ←Digits.Succ]
    rw[Digits.Succ_toOneBaseNat_eq_toOneBaseNat_cons_zero]
    rw[Digits.append]
    rw[Digits.toNat]
    simp[Digit.toNat]
  }
}

theorem exp_sub_one_toFrac_eq_den_mul_3(n:Digits){x:Digits}(e:int)(h:x≠ε):(⟨n,x,e - int.One,h⟩:cyc).toFrac =F ⟨(⟨n, x, e, h⟩:cyc).toFrac.num, (⟨n, x, e, h⟩:cyc).toFrac.den * 3, Nat.mul_ne_zero (⟨n, x, e, h⟩:cyc).toFrac.inv Nat.noConfusion⟩:=by{
  apply Frac.eq.symm
  have h': e - int.One + int.One =I e:=int.sub_add_cancel e int.One
  have h'':⟨n,x,e,h⟩ =F ⟨n,x,e-int.One+int.One,h⟩:=exp_int_eq_fraceq n h h'.symm
  rw[fraceq] at h''
  have h'':=h''.trans (exp_add_one_toFrac_eq_num_mul_3 _ _ _)
  simp[Frac.eq] at *
  rw[Nat.mul_left_comm] at h''
  rw[Nat.mul_comm] at h''
  exact h''
}

theorem exp_eq_cancel(m n:Digits){x y:Digits}(e:int)(hx:x ≠ ε)(hy:y ≠ ε)(h:⟨m, x, e, hx⟩ =F ⟨n, y, e, hy⟩):⟨m, x, int.Zero, hx⟩ =F ⟨n, y, int.Zero, hy⟩:=by{
  simp[fraceq, toFrac, int.Zero, Digits.toOneBaseNat, Frac.eq]
  match e with
  | ⟨i, true⟩ => {
    simp[fraceq, toFrac, Frac.eq] at h
    repeat rw[Digits.nat_eq_iff_toNat_eq.mp (Digits.padtailzero_nat_eq_mul_one_pad_zero _ (Digits.toOneBaseNat_isZero _))] at h
    repeat rw[Digits.mul_toNat_eq_toNat_mul] at h
    rw[Nat.mul_comm] at h
    rw[←Nat.mul_assoc] at h
    rw[←Nat.mul_assoc] at h
    have h':0<(ε::(1) ++ i.toOneBaseNat).toNat:=by{
      have h':=Digits.one_pad_zero_not_zero i
      rw[Digits.isZero_iff_toNat_eq_zero] at h'
      exact Nat.ne_zero_iff_gt_zero.mp h'
    }
    have h:=Nat.eq_of_mul_eq_mul_right h' h
    apply λ h' => Eq.trans h' h
    exact Nat.mul_comm _ _
  }
  | ⟨i, false⟩ => {
    simp[fraceq, toFrac, Frac.eq] at h
    repeat rw[Digits.nat_eq_iff_toNat_eq.mp (Digits.padtailzero_nat_eq_mul_one_pad_zero _ (Digits.toOneBaseNat_isZero _))] at h
    repeat rw[Digits.mul_toNat_eq_toNat_mul] at h
    have h:=h.symm
    rw[Nat.mul_comm] at h
    rw[←Nat.mul_assoc] at h
    rw[←Nat.mul_assoc] at h
    have h':0<(ε::(1) ++ i.toOneBaseNat).toNat:=by{
      have h':=Digits.one_pad_zero_not_zero i
      rw[Digits.isZero_iff_toNat_eq_zero] at h'
      exact Nat.ne_zero_iff_gt_zero.mp h'
    }
    have h:=Nat.eq_of_mul_eq_mul_right h' h
    apply Eq.symm
    apply λ h' => Eq.trans h' h
    exact Nat.mul_comm _ _
  }
}

theorem exp_eq_congr(m n:Digits){x y:Digits}(e:int)(hx:x ≠ ε)(hy:y ≠ ε)(h:⟨m, x, int.Zero, hx⟩ =F ⟨n, y, int.Zero, hy⟩):⟨m, x, e, hx⟩ =F ⟨n, y, e, hy⟩:=by{
  match e with
  | ⟨i, true⟩ => {
    simp[fraceq, toFrac, Frac.eq] at *
    simp[Digits.toOneBaseNat, int.Zero] at h
    repeat rw[Digits.nat_eq_iff_toNat_eq.mp (Digits.padtailzero_nat_eq_mul_one_pad_zero _ (Digits.toOneBaseNat_isZero _))]
    repeat rw[Digits.mul_toNat_eq_toNat_mul]
    rw[←Nat.mul_assoc]
    rw[←h]
    rw[Nat.mul_assoc, Nat.mul_assoc]
    rw[Nat.mul_comm ( ε :: (1) ++ i.toOneBaseNat).toNat]
  }
  | ⟨i, false⟩ => {
    simp[fraceq, toFrac, Frac.eq] at *
    simp[Digits.toOneBaseNat, int.Zero] at h
    repeat rw[Digits.nat_eq_iff_toNat_eq.mp (Digits.padtailzero_nat_eq_mul_one_pad_zero _ (Digits.toOneBaseNat_isZero _))]
    repeat rw[Digits.mul_toNat_eq_toNat_mul]
    apply Eq.symm
    rw[←Nat.mul_assoc]
    rw[h]
    rw[Nat.mul_assoc, Nat.mul_assoc]
    rw[Nat.mul_comm ( ε :: (1) ++ i.toOneBaseNat).toNat]
  }
}

theorem movl_fraceq{x:Digits}(hn:x ≠ ε)(hc:x.minCyc = x)(e:int):⟨ε, x, e, hn⟩ =F movl hn hc e:=by{
  rw[movl]
  cases Decidable.em (Digits.heads hn = ε) with
  | inl h0 => {
    simp[h0]
    cases Decidable.em (Digits.tail hn = (0)) with
    | inl h1 => {
      simp[h1]
      match e with
      | ⟨i, true⟩ => {
        simp[fraceq, toFrac, Frac.eq]
        match x with
        | _::_ => {
          simp[Digits.heads] at h0
          simp[Digits.tail] at h1
          simp[h0, h1] at *
          simp[Digits.toNegOne]
          simp[int.Zero, Digits.toOneBaseNat]
          simp[Digits.add_toNat_eq_toNat_add, Digits.mul_toNat_eq_toNat_mul]
          simp[Digits.toNat, Digit.toNat]
        }
      }
      | ⟨i, false⟩ => {
        simp[fraceq, toFrac, Frac.eq]
        match x with
        | _::_ => {
          simp[Digits.heads] at h0
          simp[Digits.tail] at h1
          simp[h0, h1] at *
          simp[Digits.toNegOne]
          simp[int.Zero, Digits.toOneBaseNat]
          simp[Digits.add_toNat_eq_toNat_add, Digits.mul_toNat_eq_toNat_mul]
          simp[Digits.toNat, Digit.toNat]
          simp[Digits.mul, Digits.mul', Digits.add, Digits.add', Digits.add'', Digit.half_add3]
          have h2:=Digits.nat_eq_iff_toNat_eq.mp (Digits.padtailzero_nat_eq_mul_one_pad_zero (ε::(0)) (Digits.toOneBaseNat_isZero i))
          rw[h2]
          rw[Digits.mul_toNat_eq_toNat_mul]
          simp[Digits.toNat, Digit.toNat]
        }
      }
    }
    | inr h1 => {
      simp[h1]
      match e with
      | ⟨i, true⟩
      | ⟨i, false⟩ => {
        simp[fraceq, toFrac, Frac.eq]
        cases Decidable.em (i.isZero) with
        | inl h => {
          simp[int.toStdInt, h, Digits.toOneBaseNat, Digits.zero_toOneBaseNat_is_ε]
          exact Nat.mul_comm _ _
        }
        | inr h => {
          simp[int.toStdInt, h]
          have h':i.toOneBaseNat = i.toStdNat.toOneBaseNat:=Digits.toOneBaseNat_eq_of_nat_eq (Digits.toStdNat_nat_eq i).symm
          rw[h']
          exact Nat.mul_comm _ _
        }
      }
    }
  }
  | inr h0 => {
    simp[h0]
    cases Decidable.em (Digits.head hn = (0)) with
    | inl h1 => {
      simp[h1]
      have hc':x.rotl.minCyc = x.rotl:=Digits.minCyc_rotl_minCyc hc
      have hn':x.rotl ≠ ε:=by{
        intro tmp
        have tmp:=Digits.rotl_cancel (tmp.trans (rfl:ε = (ε).rotl):_ = (ε).rotl)
        exact hn tmp
      }
      have : Digits.headzerocountLt (x.rotl) x:=by{
        have : x.rotl.headzerocount.Succ =N x.headzerocount:=by{
          simp[Digits.rotl] at *
          apply Digits.nat.eq.symm
          rw[Digits.headzerocount]
          simp[hn,h1]
          rw[Digits.Succ, Digits.Succ]
          apply λ h => Digits.nat.eq_of_eq_add_eq h (Digits.nat.eq.refl Digits.One)
          have tmp : ¬(Digits.tails hn).isZero:=by {
            match x with | x'::d' => {
              simp[Digits.heads] at h0
              simp at hc'
              intro hf
              have tmp : ¬ x'.isZero:=by{
                rw[←Digits.tails.cons_tails h0] at hf
                rw[Digits.isZero] at hf
                simp[hf.right] at *
                rw[Digits.tails.cons_tails Digits.noConfusion] at hc'
                have h'':(Digits.tails (Digits.noConfusion:(x'::(0))::(0) ≠ ε)).isZero:=by{
                  rw[←Digits.tails.cons_tails]
                  rw[←Digits.tails.cons_tails h0]
                  simp[Digits.isZero]
                  exact hf
                }
                rw[h1] at hc'
                have h''':(Digits.tails (Digits.noConfusion:(x'::(0))::(0) ≠ ε)) = ε ∨ (Digits.tails (Digits.noConfusion:(x'::(0))::(0) ≠ ε)) = ε::(0) := Digits.isZero_minCyc_eq_self h'' hc'
                rw[←Digits.tails.cons_tails Digits.noConfusion] at h'''
                simp at h'''
                rw[←Digits.tails.cons_tails h0] at h'''
                contradiction
              }
              apply tmp
              have h':Digits.head h0 = (0):=by{
                rw[Digits.head.cons_head]
                exact h1
              }
              have h'':=Digits.eq_head_append_tails h0
              rw[←h'', h']
              have h':(ε::(0)).isZero:=by simp
              rw[←Digits.tails.cons_tails h0] at hf
              rw[Digits.isZero] at hf
              exact Digits.zero_append_zero_isZero h' hf.left
            }
          }
          rw[Digits.notZero_cons_zero_headzerocount_eq tmp]
          exact Digits.nat.eq.refl _
        }
        exact Digits.nat.lt_iff_Succ_le.mpr this.to_le
      }
      apply λ h => fraceq.trans h (movl_fraceq (Digits.not_ε_rotl hn) (Digits.minCyc_rotl_minCyc hc) (e - int.One).toStdInt)
      apply (toStdInt_fraceq ε e hn).trans
      apply fraceq.symm
      apply (exp_int_eq_fraceq _ _ (int.sub_toStdInt_eq_toStdInt_sub _ _)).trans
      rw[int.One_toStdInt]
      apply (exp_sub_one_toFrac_eq_den_mul_3 _ _ _).trans
      match e.toStdInt with
      | ⟨i, true⟩ => {
        simp[toFrac]
        simp[Digits.nat_eq_iff_toNat_eq.mp (Digits.padtailzero_nat_eq_mul_one_pad_zero _ (Digits.toOneBaseNat_isZero i))]
        simp[Digits.mul_toNat_eq_toNat_mul]
        simp[Frac.eq]
        simp[Digits.toNegOne_eq_of_len_eq (Digits.rotl_len_eq x)]
        apply Eq.symm
        rw[Nat.mul_comm]
        repeat rw[Nat.mul_assoc]
        apply congrArg (λ y => x.toNegOne.toNat * y)
        apply congrArg (λ y => (ε::(1) ++ i.toOneBaseNat).toNat * y)
        simp[Digits.add_toNat_eq_toNat_add, Digits.mul_toNat_eq_toNat_mul, Nat.mul_add, Digits.toNat]
        rw[Digits.rotl]
        simp[hn, h1]
        simp[Digits.toNat, Digit.toNat]
        rw[Nat.mul_comm]
        apply congrArg (λ y => 3 * y)
        rw[←Digits.nat_eq_iff_toNat_eq]
        apply Digits.nat.eq.symm
        apply (Digits.toStdNat_nat_eq x).symm.trans
        rw[Digits.toStdNat]
        simp[hn, h1]
        exact Digits.toStdNat_nat_eq _
      }
      | ⟨i, false⟩ => {
        simp[toFrac]
        repeat rw[Digits.nat_eq_iff_toNat_eq.mp (Digits.padtailzero_nat_eq_mul_one_pad_zero _ (Digits.toOneBaseNat_isZero _))]
        simp[Digits.mul_toNat_eq_toNat_mul]
        simp[Frac.eq]
        simp[Digits.toNegOne_eq_of_len_eq (Digits.rotl_len_eq x)]
        apply Eq.symm
        rw[Nat.mul_comm]
        repeat rw[Nat.mul_assoc]
        apply congrArg (λ y => x.toNegOne.toNat * y)
        rw[Digits.nat_eq_iff_toNat_eq.mp (Digits.padtailzero_nat_eq_mul_one_pad_zero ( ε * x.toNegOne + x) (Digits.toOneBaseNat_isZero _))]
        simp[Digits.mul_toNat_eq_toNat_mul]
        rw[←Nat.mul_assoc]
        apply congrArg (λ y => y * (ε::(1) ++ i.toOneBaseNat).toNat)
        simp[Digits.add_toNat_eq_toNat_add, Digits.mul_toNat_eq_toNat_mul, Nat.mul_add, Digits.toNat]
        rw[Digits.rotl]
        simp[hn, h1]
        simp[Digits.toNat, Digit.toNat]
        rw[Nat.mul_comm]
        apply congrArg (λ y => 3 * y)
        rw[←Digits.nat_eq_iff_toNat_eq]
        apply Digits.nat.eq.symm
        apply (Digits.toStdNat_nat_eq x).symm.trans
        rw[Digits.toStdNat]
        simp[hn, h1]
        exact Digits.toStdNat_nat_eq _
      }
    }
    | inr h1 => {
      simp[h1]
      match e with
      | ⟨i, true⟩
      | ⟨i, false⟩ => {
        simp[fraceq, toFrac, Frac.eq]
        cases Decidable.em (i.isZero) with
        | inl h => {
          simp[int.toStdInt, h, Digits.toOneBaseNat, Digits.zero_toOneBaseNat_is_ε]
          exact Nat.mul_comm _ _
        }
        | inr h => {
          simp[int.toStdInt, h]
          have h':i.toOneBaseNat = i.toStdNat.toOneBaseNat:=Digits.toOneBaseNat_eq_of_nat_eq (Digits.toStdNat_nat_eq i).symm
          rw[h']
          exact Nat.mul_comm _ _
        }
      }
    }
  }
}
termination_by' {
  rel:=λ x y:(_:Digits) ×' _ => Digits.headzerocountLt x.fst y.fst
  wf:=InvImage.wf (λ x:(_:Digits) ×' _ => x.fst) Digits.headzerocountLt.wf
}

theorem movr_fraceq{n x:Digits}(h0:n.isStdNat)(h1:n ≠ ε)(h2:x ≠ ε)(h3:x.minCyc = x)(e:int):⟨n, x, e, h2⟩ =F movr h0 h1 h2 h3 e:=by{
  rw[movr]
  cases Decidable.em (Digits.tail h1 = Digits.tail h2) with
  | inl h3 => {
    simp[h3]
    cases Decidable.em (Digits.heads h1 = ε) with
    | inl h4 => {
      simp[h4]
      have h5:Digits.tail h1 ≠ (0):=by{
        intro h
        match n with
        | n'::d => {
          simp[Digits.heads] at h4
          simp[Digits.tail] at h
          simp[h4, h] at h0
          rw[Digits.isStdNat] at h0
          simp at h0
        }
      }
      match n with
      | n'::(0) => simp[Digits.tail] at h5
      | n'::(1) => {
        simp[Digits.heads] at h4
        simp[h4]
        apply (exp_int_eq_fraceq _ _ (int.toStdInt_eq e)).symm.trans
        apply fraceq.symm
        apply (exp_int_eq_fraceq _ _ (int.add_toStdInt_eq_toStdInt_add _ _)).trans
        simp[int.One_toStdInt]
        rw[fraceq]
        apply (exp_add_one_toFrac_eq_num_mul_3 _ _ _).trans
        match e.toStdInt with
        | ⟨i, true⟩ => {
          simp[toFrac, Frac.eq]
          repeat rw[Digits.nat_eq_iff_toNat_eq.mp (Digits.padtailzero_nat_eq_mul_one_pad_zero _ (Digits.toOneBaseNat_isZero _))]
          repeat rw[Digits.mul_toNat_eq_toNat_mul]
          rw[Nat.mul_comm]
          rw[←Nat.mul_assoc]
          rw[←Nat.mul_assoc]
          apply congrArg (λ y => y * (ε::(1) ++ i.toOneBaseNat).toNat)
          simp[Digits.add_toNat_eq_toNat_add, Digits.mul_toNat_eq_toNat_mul, Nat.add_mul]
          simp[Digits.toNat, Digit.toNat]
          rw[Digits.toNegOne_eq_of_len_eq (Digits.rotr_len_eq x)]
          rw[←Nat.add_mul]
          apply congrArg (λ y => y * x.toNegOne.toNat)
          match x with
          | x'::d' => {
            simp[Digits.tail] at h3
            simp[←h3]
            simp[Digits.rotr]
            rw[Digits.toNat]
            simp[Digit.toNat]
            have h6:ε::(1) ++ x' =N (ε::(1) ++ x'.toZero) + x':=by{
              have h6:=Digits.cutTails_padtailzero_add_getTails_nat_eq (ε::(1) ++ x') x'
              simp[Digits.append_cutTails_cancel] at h6
              simp[Digits.append_getTails] at h6
              exact h6.symm
            }
            rw[Digits.nat_eq_iff_toNat_eq.mp h6]
            simp[Digits.add_toNat_eq_toNat_add]
            simp[Nat.add_mul]
            rw[Nat.add_comm (x'.toNat * 3)]
            rw[←Nat.add_assoc]
            apply congrArg (λ y => y + Nat.mul x'.toNat 3)
            rw[←Digits.toNegOne_add_One_eq_one_pad_zero]
            simp[Digits.add_toNat_eq_toNat_add]
            simp[Digits.One, Digits.toNat, Digit.toNat]
            rw[Nat.add_assoc]
            simp[Nat.add_mul]
          }
        }
        | ⟨i, false⟩ => {
          simp[toFrac, Frac.eq]
          repeat rw[Digits.nat_eq_iff_toNat_eq.mp (Digits.padtailzero_nat_eq_mul_one_pad_zero _ (Digits.toOneBaseNat_isZero _))]
          repeat rw[Digits.mul_toNat_eq_toNat_mul]
          rw[Nat.mul_comm]
          repeat rw[Nat.mul_assoc]
          repeat rw[Nat.mul_left_comm _ (ε::(1) ++ i.toOneBaseNat).toNat]
          apply congrArg (λ y => (ε::(1) ++ i.toOneBaseNat).toNat * y)
          rw[Digits.toNegOne_eq_of_len_eq (Digits.rotr_len_eq x)]
          repeat rw[←Nat.mul_assoc]
          apply congrArg (λ y => y * x.toNegOne.toNat)
          simp[Digits.add_toNat_eq_toNat_add, Digits.mul_toNat_eq_toNat_mul]
          simp[Digits.toNat, Digit.toNat]
          match x with
          | x'::d' => {
            have h6:ε::(1) ++ x' =N (ε::(1) ++ x'.toZero) + x':=by{
              have h6:=Digits.cutTails_padtailzero_add_getTails_nat_eq (ε::(1) ++ x') x'
              simp[Digits.append_cutTails_cancel] at h6
              simp[Digits.append_getTails] at h6
              exact h6.symm
            }
            simp[Digits.rotr]
            simp[Digits.tail] at h3
            simp[←h3]
            rw[Digits.nat_eq_iff_toNat_eq.mp h6]
            simp[Digits.add_toNat_eq_toNat_add]
            rw[Nat.add_mul]
            simp[Digits.toNat, Digit.toNat]
            rw[Nat.add_comm (x'.toNat * 3)]
            rw[←Nat.add_assoc]
            apply congrArg (λ y => y + Nat.mul x'.toNat 3)
            rw[←Digits.toNegOne_add_One_eq_one_pad_zero]
            simp[Digits.add_toNat_eq_toNat_add]
            simp[Digits.One, Digits.toNat, Digit.toNat]
            rw[Nat.add_assoc]
            simp[Nat.add_mul]
          }
        }
      }
      | n'::(2) => {
        simp[Digits.heads] at h4
        simp[h4]
        apply (exp_int_eq_fraceq _ _ (int.toStdInt_eq e)).symm.trans
        apply fraceq.symm
        apply (exp_int_eq_fraceq _ _ (int.add_toStdInt_eq_toStdInt_add _ _)).trans
        simp[int.One_toStdInt]
        rw[fraceq]
        apply (exp_add_one_toFrac_eq_num_mul_3 _ _ _).trans
        match e.toStdInt with
        | ⟨i, true⟩ => {
          simp[toFrac, Frac.eq]
          repeat rw[Digits.nat_eq_iff_toNat_eq.mp (Digits.padtailzero_nat_eq_mul_one_pad_zero _ (Digits.toOneBaseNat_isZero _))]
          repeat rw[Digits.mul_toNat_eq_toNat_mul]
          rw[Nat.mul_comm]
          rw[←Nat.mul_assoc]
          rw[←Nat.mul_assoc]
          apply congrArg (λ y => y * (ε::(1) ++ i.toOneBaseNat).toNat)
          simp[Digits.add_toNat_eq_toNat_add, Digits.mul_toNat_eq_toNat_mul, Nat.add_mul]
          simp[Digits.toNat, Digit.toNat]
          rw[Digits.toNegOne_eq_of_len_eq (Digits.rotr_len_eq x)]
          rw[←Nat.add_mul]
          apply congrArg (λ y => y * x.toNegOne.toNat)
          match x with
          | x'::d' => {
            simp[Digits.tail] at h3
            simp[←h3]
            simp[Digits.toNat, Digit.toNat, Digits.rotr]
            have h6:ε::(2) ++ x' =N (ε::(2) ++ x'.toZero) + x':=by{
              have h6:=Digits.cutTails_padtailzero_add_getTails_nat_eq (ε::(2) ++ x') x'
              simp[Digits.append_cutTails_cancel] at h6
              simp[Digits.append_getTails] at h6
              exact h6.symm
            }
            rw[Digits.nat_eq_iff_toNat_eq.mp h6]
            simp[Digits.add_toNat_eq_toNat_add]
            rw[Nat.add_mul]
            rw[Nat.add_comm (x'.toNat * 3)]
            rw[←Nat.add_assoc]
            apply congrArg (λ y:Nat => y + x'.toNat * 3)
            rw[Digits.nat_eq_iff_toNat_eq.mp (Digits.one_pad_zero_mul_two_nat_eq_two_pad_zero (Digits.toZero_isZero x')).symm]
            simp[Digits.mul_toNat_eq_toNat_mul]
            simp[Digits.toNat, Digit.toNat]
            rw[←Digits.toNegOne_add_One_eq_one_pad_zero]
            simp[Digits.add_toNat_eq_toNat_add]
            simp[Nat.add_mul, Nat.mul_add, Digits.One, Digits.toNat, Digit.toNat]
            rw[Nat.mul_left_comm]
            rw[←Nat.mul_assoc]
          }
        }
        | ⟨i, false⟩ => {
          simp[toFrac, Frac.eq]
          repeat rw[Digits.nat_eq_iff_toNat_eq.mp (Digits.padtailzero_nat_eq_mul_one_pad_zero _ (Digits.toOneBaseNat_isZero _))]
          repeat rw[Digits.mul_toNat_eq_toNat_mul]
          rw[Digits.toNegOne_eq_of_len_eq (Digits.rotr_len_eq x)]
          apply Eq.symm
          rw[Nat.mul_comm]
          apply congrArg (λ y => x.toNegOne.toNat * y)
          rw[Nat.mul_assoc]
          rw[Nat.mul_comm _ 3]
          rw[←Nat.mul_assoc]
          apply congrArg (λ y => y * (ε::(1) ++ i.toOneBaseNat).toNat)
          simp[Digits.add_toNat_eq_toNat_add, Digits.mul_toNat_eq_toNat_mul]
          match x with
          | x'::d' => {
            simp[Digits.tail] at h3
            simp[←h3]
            simp[Digits.rotr, Digits.toNat, Digit.toNat]
            have h6:ε::(2) ++ x' =N (ε::(2) ++ x'.toZero) + x':=by{
              have h6:=Digits.cutTails_padtailzero_add_getTails_nat_eq (ε::(2) ++ x') x'
              simp[Digits.append_cutTails_cancel] at h6
              simp[Digits.append_getTails] at h6
              exact h6.symm
            }
            rw[Digits.nat_eq_iff_toNat_eq.mp h6]
            simp[Digits.add_toNat_eq_toNat_add]
            simp[Nat.add_mul]
            rw[Nat.add_comm (x'.toNat * 3) 2]
            rw[←Nat.add_assoc]
            apply congrArg (λ y:Nat => y + x'.toNat * 3)
            rw[Digits.nat_eq_iff_toNat_eq.mp (Digits.one_pad_zero_mul_two_nat_eq_two_pad_zero (Digits.toZero_isZero x')).symm]
            simp[Digits.mul_toNat_eq_toNat_mul]
            simp[Digits.toNat, Digit.toNat]
            rw[←Digits.toNegOne_add_One_eq_one_pad_zero]
            simp[Digits.add_toNat_eq_toNat_add]
            simp[Nat.add_mul, Nat.mul_add, Digits.One, Digits.toNat, Digit.toNat]
            rw[Nat.mul_left_comm]
            exact Nat.mul_assoc _ _ _
          }
        }
      }
    }
    | inr h4 => {
      simp[h4]
      have h0':=Digits.isStdNat_heads_isStdNat h1 h0
      have h1':=h4
      have h2':x.rotr ≠ ε:=by{rw[Digits.rotr_iff_rotr', Digits.rotr'];simp[h2];exact Digits.not_ε_append Digits.noConfusion _}
      have h3':=Digits.minCyc_rotr_minCyc (by assumption:Digits.minCyc x = x)
      have : (Digits.heads h1) <L n:=by{
        match n with
        | _::_ => simp[Digits.heads]; exact Digits.len.lt_cons _ _
      }
      apply λ h => fraceq.trans h (movr_fraceq h0' h1' h2' h3' (e + int.One).toStdInt)
      apply (toStdInt_fraceq n e h2).trans
      apply fraceq.symm
      apply (exp_int_eq_fraceq _ _ (int.add_toStdInt_eq_toStdInt_add _ _)).trans
      rw[int.One_toStdInt]
      apply (exp_add_one_toFrac_eq_num_mul_3 _ _ _).trans
      match e.toStdInt with
      | ⟨i, true⟩ => {
        simp[toFrac, Frac.eq]
        rw[Digits.toNegOne_eq_of_len_eq (Digits.rotr_len_eq x)]
        rw[Nat.mul_comm]
        apply congrArg (λ y => y * (x.toNegOne ++ i.toOneBaseNat).toNat)
        match n, x with
        | n'::nd, x'::xd => {
          simp[Digits.heads, Digits.tail] at *
          simp[h3]
          simp[Digits.rotr]
          simp[Digits.add_toNat_eq_toNat_add]
          have h5:ε::xd ++ x' =N (ε::xd ++ x'.toZero) + x':=by{
            have h5:=Digits.cutTails_padtailzero_add_getTails_nat_eq (ε::xd ++ x') x'
            simp[Digits.append_cutTails_cancel] at h5
            simp[Digits.append_getTails] at h5
            exact h5.symm
          }
          rw[Digits.nat_eq_iff_toNat_eq.mp h5]
          simp[Digits.add_toNat_eq_toNat_add, Digits.mul_toNat_eq_toNat_mul]
          simp[Nat.add_mul, Nat.mul_add]
          simp[Digits.toNat]
          rw[Nat.add_comm (x'.toNat * 3) xd.toNat]
          repeat rw[←Nat.add_assoc]
          apply congrArg (λ y:Nat => y + x'.toNat * 3)
          simp[Nat.add_mul, Nat.mul_add]
          repeat rw[Nat.add_assoc]
          rw[Nat.mul_assoc]
          rw[Nat.mul_left_comm 3]
          rw[Nat.mul_assoc, Nat.mul_assoc, ←Nat.mul_assoc _ 3 3]
          repeat rw[Nat.add_assoc]
          apply congrArg (λ y => n'.toNat * (x'.toNegOne.toNat * 3 * 3) + y)
          rw[Nat.add_left_comm]
          rw[Nat.mul_comm 3]
          rw[←Nat.mul_assoc]
          apply congrArg (λ y:Nat => n'.toNat * (2).toNat * 3 + y)
          have h6:xd.toNat * (2).toNat + xd.toNat = xd.toNat * 3:=by{
            match xd with
            | (0) | (1) | (2) => simp[Digit.toNat]
          }
          rw[h6]
          rw[←Nat.mul_add]
          have h7:x'.toNegOne.toNat * 3 + 3 = (x'.toNegOne + Digits.One).toNat * 3:=by{
            rw[Digits.add_toNat_eq_toNat_add]
            simp[Nat.add_mul, Digits.One, Digits.toNat, Digit.toNat]
          }
          rw[h7]
          rw[Digits.toNegOne_add_One_eq_one_pad_zero]
          rw[←Nat.mul_assoc]
          apply congrArg (λ y => y * 3)
          rw[Digits.Digit_toNat_eq_Digits_toNat]
          rw[←Digits.mul_toNat_eq_toNat_mul]
          rw[←Digits.nat_eq_iff_toNat_eq]
          exact (Digits.padtailzero_nat_eq_mul_one_pad_zero (ε::xd) (Digits.toZero_isZero x')).symm
        }
      }
      | ⟨i, false⟩ => {
        simp[toFrac, Frac.eq]
        rw[Digits.toNegOne_eq_of_len_eq (Digits.rotr_len_eq x)]
        apply Eq.symm
        rw[Nat.mul_comm]
        apply congrArg (λ y => x.toNegOne.toNat * y)
        repeat rw[Digits.nat_eq_iff_toNat_eq.mp (Digits.padtailzero_nat_eq_mul_one_pad_zero _ (Digits.toOneBaseNat_isZero _))]
        rw[Digits.mul_toNat_eq_toNat_mul]
        rw[Digits.mul_toNat_eq_toNat_mul]
        rw[Nat.mul_assoc, Nat.mul_comm _ 3, ←Nat.mul_assoc]
        apply congrArg (λ y:Nat => y * (ε::(1) ++ i.toOneBaseNat).toNat)
        match n, x with
        | n'::nd, x'::xd => {
          simp[Digits.heads, Digits.tail] at *
          simp[Digits.rotr]
          simp[Digits.add_toNat_eq_toNat_add, Digits.mul_toNat_eq_toNat_mul]
          have h5:ε::xd ++ x' =N (ε::xd ++ x'.toZero) + x':=by{
            have h5:=Digits.cutTails_padtailzero_add_getTails_nat_eq (ε::xd ++ x') x'
            simp[Digits.append_cutTails_cancel] at h5
            simp[Digits.append_getTails] at h5
            exact h5.symm
          }
          rw[Digits.nat_eq_iff_toNat_eq.mp h5]
          simp[Digits.add_toNat_eq_toNat_add]
          simp[Nat.add_mul]
          simp[Digits.toNat]
          simp[h3]
          rw[Nat.add_comm (x'.toNat * 3) xd.toNat]
          repeat rw[←Nat.add_assoc]
          apply congrArg (λ y:Nat => y + x'.toNat * 3)
          simp[Nat.add_mul, Nat.mul_add]
          repeat rw[Nat.add_assoc]
          repeat rw[Nat.mul_assoc]
          rw[Nat.mul_left_comm 3]
          apply congrArg (λ y => n'.toNat * (x'.toNegOne.toNat * (3 * 3)) + y)
          rw[Nat.add_left_comm]
          rw[Nat.mul_comm (2).toNat]
          apply congrArg (λ y => n'.toNat * (3 * (2).toNat) + y)
          have h6:xd.toNat * (2).toNat + xd.toNat = xd.toNat * 3:=by{
            match xd with
            | (0) | (1) | (2) => simp[Digit.toNat]
          }
          rw[h6]
          rw[←Nat.mul_add]
          have h7:x'.toNegOne.toNat * 3 + 3 = (x'.toNegOne + Digits.One).toNat * 3:=by{
            rw[Digits.add_toNat_eq_toNat_add]
            simp[Nat.add_mul, Digits.One, Digits.toNat, Digit.toNat]
          }
          rw[h7]
          rw[Digits.toNegOne_add_One_eq_one_pad_zero]
          rw[←Nat.mul_assoc]
          apply congrArg (λ y => y * 3)
          rw[Digits.Digit_toNat_eq_Digits_toNat]
          rw[←Digits.mul_toNat_eq_toNat_mul]
          rw[←Digits.nat_eq_iff_toNat_eq]
          exact Digits.padtailzero_nat_eq_mul_one_pad_zero (ε::xd) (Digits.toZero_isZero x')
        }
      }
    }
  }
  | inr h3 => {
    simp[h3]
    apply (exp_int_eq_fraceq _ _ (int.toStdInt_eq e)).symm.trans
    exact fraceq.refl _
  }
}
termination_by' {
  rel:=λ x y => x.fst <L y.fst
  wf:=InvImage.wf (λ x:(_:Digits) ×' _ => x.fst) Digits.len.lt.wf
}

theorem toStdCyc_fraceq(c:cyc):c.toStdCyc =F c:=by{
  match c with
  | ⟨n, x, e, h⟩ => {
    simp[toStdCyc]
    apply fraceq.symm
    apply (toStdNat_fraceq _ _ _).trans
    apply (toStdInt_fraceq _ _ _).trans
    apply (minCyc_fraceq _ _ _).trans
    apply fraceq.symm
    cases Decidable.em (n.toStdNat = ε) with
    | inl h' => {
      simp[h']
      apply (movl_fraceq _ _ e.toStdInt).symm.trans
      exact fraceq.refl _
    }
    | inr h' => {
      simp[h']
      apply (movr_fraceq _ _ _ _ _).symm.trans
      exact fraceq.refl _
    }
  }
}

theorem fraceq_of_cyc_eq{x y:cyc}(h:x =C y):x =F y:=by{
  have h0:=toStdCyc_fraceq x
  have h1:=toStdCyc_fraceq y
  rw[eq] at h
  rw[h] at h0
  exact h0.symm.trans h1
}
end cyc
end wkmath
