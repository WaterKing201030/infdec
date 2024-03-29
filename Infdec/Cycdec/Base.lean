import Infdec.Integer
namespace wkmath
structure cyc where
  pre:Digits
  post:Digits
  exp:int
  inv:post ≠ ε

namespace Digits
def headzerocount(x:Digits):Digits:=
  if h:x = ε then ε
  else if head h = (0) then
    have : (tails h) <L x:=tails_len_lt h
    (headzerocount (tails h)).Succ
  else ε
termination_by' {
  rel:=len.lt
  wf:=len.lt.wf
}

theorem notZero_cons_zero_headzerocount_eq{x:Digits}(h:¬x.isZero):(x::(0)).headzerocount = x.headzerocount:=by{
  induction x using tails.recursion with
  | base => contradiction
  | ind x h' ih => {
    have h0:(tails h')::(0) = (tails (Digits.noConfusion:x::(0) ≠ ε)):=tails.cons_tails _ _
    rw[headzerocount, headzerocount]
    simp[h']
    have h1:head h' = head (Digits.noConfusion:x::(0) ≠ ε):=head.cons_head _ _
    cases Decidable.em (head h' = (0)) with
    | inl h'' => {
      rw[←h1]
      simp[h'']
      apply congrArg
      rw[←h0]
      apply ih
      intro hf
      apply h
      rw[←eq_head_append_tails h']
      rw[h'']
      have : (ε::(0)).isZero := by simp
      exact zero_append_zero_isZero this hf
    }
    | inr h'' => rw[←h1]; simp[h'']
  }
}

def headzerocountLt(x y:Digits):=
  x.headzerocount < y.headzerocount

@[inline] instance headzerocountLt.wf:WellFounded headzerocountLt:=
  InvImage.wf (λ x:Digits => x.headzerocount) nat.lt.wf
end Digits

namespace cyc

def Zero:cyc:=⟨ε, ε::(0), ⟨ε, false⟩, Digits.noConfusion⟩

def movl{x:Digits}(hn:x ≠ ε)(hc:x.minCyc = x)(e:int):cyc:=
  if h:(Digits.heads hn) = ε then
    if (Digits.tail hn) = (0) then
      ⟨ε, ε::(0), int.Zero, Digits.noConfusion⟩
    else
    ⟨ε, x, e.toStdInt, hn⟩
  else if h':Digits.head hn = (0) then
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
        simp[hn,h']
        rw[Digits.Succ, Digits.Succ]
        apply λ h => Digits.nat.eq_of_eq_add_eq h (Digits.nat.eq.refl Digits.One)
        have tmp : ¬(Digits.tails hn).isZero:=by {
          match x with | x'::d' => {
            simp[Digits.heads] at h
            simp at hc'
            intro hf
            have tmp : ¬ x'.isZero:=by{
              rw[←Digits.tails.cons_tails h] at hf
              rw[Digits.isZero] at hf
              simp[hf.right] at *
              rw[Digits.tails.cons_tails Digits.noConfusion] at hc'
              have h'':(Digits.tails (Digits.noConfusion:(x'::(0))::(0) ≠ ε)).isZero:=by{
                rw[←Digits.tails.cons_tails]
                rw[←Digits.tails.cons_tails h]
                simp[Digits.isZero]
                exact hf
              }
              rw[h'] at hc'
              have h''':(Digits.tails (Digits.noConfusion:(x'::(0))::(0) ≠ ε)) = ε ∨ (Digits.tails (Digits.noConfusion:(x'::(0))::(0) ≠ ε)) = ε::(0) := Digits.isZero_minCyc_eq_self h'' hc'
              rw[←Digits.tails.cons_tails Digits.noConfusion] at h'''
              simp at h'''
              rw[←Digits.tails.cons_tails h] at h'''
              contradiction
            }
            apply tmp
            have h':Digits.head h = (0):=by{
              rw[Digits.head.cons_head]
              exact h'
            }
            have h'':=Digits.eq_head_append_tails h
            rw[←h'', h']
            have h':(ε::(0)).isZero:=by simp
            rw[←Digits.tails.cons_tails h] at hf
            rw[Digits.isZero] at hf
            exact Digits.zero_append_zero_isZero h' hf.left
          }
        }
        rw[Digits.notZero_cons_zero_headzerocount_eq tmp]
        exact Digits.nat.eq.refl _
      }
      exact Digits.nat.lt_iff_Succ_le.mpr this.to_le
    }
    movl hn' hc' (e - int.One).toStdInt
  else
    ⟨ε, x, e.toStdInt, hn⟩
termination_by' {
  rel:=λ x y:(_:Digits) ×' _ => Digits.headzerocountLt x.fst y.fst
  wf:=InvImage.wf (λ x:(_:Digits) ×' _ => x.fst) Digits.headzerocountLt.wf
}

def movr{n x:Digits}(hd:n.isStdNat)(hn:n ≠ ε)(hx:x ≠ ε)(hc:x.minCyc = x)(e:int):cyc:=
  if (Digits.tail hn) = (Digits.tail hx) then
    if h:(Digits.heads hn) = ε then
      ⟨ε, x.rotr, (e + int.One).toStdInt, by{rw[Digits.rotr_iff_rotr', Digits.rotr'];simp[hx];exact Digits.not_ε_append Digits.noConfusion _}⟩
    else
      have h':x.rotr ≠ ε:=by{rw[Digits.rotr_iff_rotr', Digits.rotr'];simp[hx];exact Digits.not_ε_append Digits.noConfusion _}
      have : (Digits.heads hn) <L n:=by{
        match n with
        | _::_ => simp[Digits.heads]; exact Digits.len.lt_cons _ _
      }
      movr (Digits.isStdNat_heads_isStdNat hn hd) h h' (Digits.minCyc_rotr_minCyc hc) (e + int.One).toStdInt
  else
    ⟨n, x, e.toStdInt, hx⟩
termination_by' {
  rel:=λ x y => x.fst <L y.fst
  wf:=InvImage.wf (λ x:(_:Digits) ×' _ => x.fst) Digits.len.lt.wf
}

def toStdCyc(c:cyc):cyc:=
  match c with
  | ⟨n, x, e, h⟩ =>
    have hn: x.minCyc ≠ ε := Digits.not_ε_minCyc_not_ε h
    have hc: (x.minCyc).minCyc = x.minCyc := Digits.minCyc.idemp x
    if h':n.toStdNat = ε then
      movl hn hc e.toStdInt
    else
      movr (Digits.toStdNat_isStdNat n) h' hn hc e.toStdInt

def eq(x y:cyc):=
  x.toStdCyc = y.toStdCyc
notation:50 lhs:51 " =C " rhs:51 => eq lhs rhs

theorem eq.refl'{a b x y:Digits}{i j:int}(h0:a =N b)(h1:x = y)(h2:i =I j)(ha:x ≠ ε)(hb:y ≠ ε):⟨a, x, i, ha⟩ =C ⟨b, y, j, hb⟩:=by{
  rw[eq]
  match x, y with | x'::xd, y'::yd => {
    simp[toStdCyc]
    have h'':i.toStdInt = j.toStdInt:=int.eq_iff_toStdInt_eq.mp h2
    rw[h'']
    simp[h1]
    cases Decidable.em (a.toStdNat = ε) with
    | inl h => {
      simp[h]
      have h':b.toStdNat = ε:=by{
        apply Digits.toStdNat.zero_to_nil
        have h:=Digits.toStdNat_ε_isZero h
        exact Digits.nat_eq_zero_isZero h0 h
      }
      simp[h']
    }
    | inr h => {
      simp[h]
      have h':b.toStdNat ≠ ε:=by{
        intro h'
        apply h
        rw[←Digits.isZero_iff_toStdNat_ε] at *
        exact Digits.nat_eq_zero_isZero' h0 h'
      }
      simp[h']
      have h''':a.toStdNat = b.toStdNat:=Digits.nat_eq_iff_toStdNat_eq.mp h0
      simp[h''']
    }
  }
}

theorem eq.refl(x:cyc):x =C x:=
  refl' (Digits.nat.eq.refl _) rfl (int.eq.refl _) x.inv x.inv

theorem eq.symm{x y:cyc}(h:x =C y):y =C x:=
  Eq.symm h

theorem eq.symm_iff{x y:cyc}:x =C y ↔ y =C x:=
  Iff.intro symm symm

theorem eq.trans{x y z:cyc}(h0:x =C y)(h1:y =C z):x =C z:=
  Eq.trans h0 h1

theorem eq.minCyc(a x:Digits)(i:int)(h:x ≠ ε):⟨a, x, i, h⟩ =C ⟨a, x.minCyc, i, Digits.not_ε_minCyc_not_ε h⟩:=by{
  rw[eq]
  match x with
  | x'::d => {
    have h':=Digits.eq_heads_cons_tail (Digits.not_ε_minCyc_not_ε h)
    have h'':(⟨a, (x'::d).minCyc, i, Digits.not_ε_minCyc_not_ε h⟩:cyc) = ⟨a, (Digits.heads (Digits.not_ε_minCyc_not_ε h))::(Digits.tail (Digits.not_ε_minCyc_not_ε h)), i, Digits.noConfusion⟩:=by simp[h']
    rw[h'']
    simp[toStdCyc]
    have h''':(x'::d).minCyc.minCyc = (x'::d).minCyc:=Digits.minCyc.idemp (x'::d)
    simp[h''', h']
  }
}

theorem eq.movr_eq(a:Digits)(d:Digit)(x:Digits)(i:int):⟨a::d, x::d, i, Digits.noConfusion⟩ =C ⟨a, (ε::d)++x, i + int.One, Digits.not_ε_append Digits.noConfusion x⟩:=by{
  rw[eq]
  have h':=Digits.eq_heads_cons_tail (Digits.not_ε_append (Digits.noConfusion:ε::d ≠ ε) x)
  have h'':(⟨a, ε::d ++ x, i + int.One, Digits.not_ε_append Digits.noConfusion x⟩:cyc) = ⟨a, (Digits.heads (Digits.not_ε_append (Digits.noConfusion:ε::d ≠ ε) x))::(Digits.tail (Digits.not_ε_append (Digits.noConfusion:ε::d ≠ ε) x)), i + int.One, Digits.noConfusion⟩:=by simp[h']
  rw[h'']
  simp[toStdCyc]
  cases Decidable.em (a.toStdNat = ε) with
  | inl h => {
    simp[h]
    match d with
    | (0) => {
      have h''':(a::(0)).toStdNat = ε:=by{
        rw[←Digits.isZero_iff_toStdNat_ε]
        simp[Digits.isZero]
        exact Digits.isZero_iff_toStdNat_ε.mpr h
      }
      simp[h''', h']
      rw[movl]
      cases Decidable.em (Digits.heads (Digits.not_ε_minCyc_not_ε (Digits.noConfusion:x::(0) ≠ ε)) = ε) with
      | inl h0 => {
        simp[h0]
        have h1:x.isZero:=by{
          have hc:(x::(0)).minCyc ≠ ε:=Digits.not_ε_minCyc_not_ε (Digits.noConfusion:x::(0) ≠ ε)
          match hc':(x::(0)).minCyc with
          | ε => contradiction
          | y::yd => {
            have hc'':(y::yd).isPostfixOf (x::(0)):=by{
              apply Digits.isCycParent_isPostfixOf
              rw[←hc']
              exact Digits.isCycParent_minCyc _
            }
            rw[Digits.isPostfixOf] at hc''
            simp[hc'] at h0
            simp[Digits.heads] at h0
            rw[h0, hc''.left] at hc'
            have hc'':(ε::(0)).isZero:=by simp
            have hc''':(x::(0)).isCycParent (Digits.minCyc (x::(0))):=Digits.isCycParent_minCyc _
            rw[←hc'] at hc''
            have hc''':=Digits.isCycParent_zero_isZero hc'' hc'''
            rw[Digits.isZero] at hc'''
            exact hc'''.left
          }
        }
        have h2:ε::(0) ++ x = x::(0):=by{
          rw[←Digits.append_tail x]
          have h2:(ε::(0)).isZero:=by simp
          exact Digits.zero_append_zero_comm h2 h1
        }
        simp[h2]
        rw[movl]
        have h3:(x::(0)).minCyc = ε::(0):=by{
          apply Digits.not_ε_isZero_minCyc Digits.noConfusion
          simp[Digits.isZero]
          exact h1
        }
        simp[h0]
        simp[h3]
        simp[Digits.tail]
      }
      | inr h0 => {
        simp[h0, Digits.eq_heads_cons_tail]
        cases Decidable.em (Digits.head (Digits.not_ε_minCyc_not_ε Digits.noConfusion:Digits.minCyc (x::(0)) ≠ ε) = (0)) with
        | inl h1 => {
          simp[h1]
          apply Eq.symm
          rw[movl]
          have h2:Digits.heads (Digits.not_ε_minCyc_not_ε (Digits.not_ε_append Digits.noConfusion x):((ε::(0))++x).minCyc ≠ ε) ≠ ε:=by{
            intro h2
            apply h0
            apply Digits.len.ε_unique
            rw[←congrArg (λ x => Digits.heads _ =L x) h2]
            apply Digits.heads_len_congr
            have h3:ε::(0) ++ x = (x::(0)).rotr:=by simp[Digits.rotr]
            rw[h3]
            rw[←Digits.rotr_minCyc_comm]
            exact (Digits.rotr_len_eq _).symm
          }
          simp[h2]
          have h3:Digits.head (Digits.not_ε_minCyc_not_ε (Digits.not_ε_append Digits.noConfusion x):(ε::(0) ++ x).minCyc ≠ ε) = (0) := by{
            rw[Digits.minCyc_head_eq_head (Digits.not_ε_append Digits.noConfusion x)]
            rw[Digits.head_of_head_append_tails]
          }
          simp[h3]
          simp[Digits.rotl_minCyc_comm]
          have h4:(ε::(0) ++ x).rotl = x::(0):=by{
            rw[Digits.rotl]
            simp[Digits.not_ε_append]
            rw[Digits.tails_of_head_append_tails, Digits.head_of_head_append_tails]
            simp
          }
          simp[h4]
          have h5:((i + int.One).toStdInt - int.One).toStdInt = i.toStdInt:=by{
            rw[←int.eq_iff_toStdInt_eq]
            rw[int.sub]
            apply (int.add_congr (int.toStdInt_eq _) (int.eq.refl _)).trans
            apply (int.add.assoc _ _ _).trans
            exact int.add_zero _ (int.add_neg_eq_zero _)
          }
          simp[h5]
          rw[movl]
          simp[h1]
          simp[h0]
          simp[Digits.rotl_minCyc_comm]
        }
        | inr h1 => {
          simp[h1]
          rw[movl]
          have h2 : Digits.heads (Digits.not_ε_minCyc_not_ε (Digits.not_ε_append Digits.noConfusion _):(ε::(0) ++ x).minCyc ≠ ε) ≠ ε:=by{
            intro h
            have h':=Digits.eq_heads_cons_tail (Digits.not_ε_minCyc_not_ε (Digits.not_ε_append (Digits.noConfusion:ε::(0) ≠ ε) x):(ε::(0) ++ x).minCyc ≠ ε)
            apply h0
            have h'':ε::(0) ++ x = (x::(0)).rotr:=rfl
            simp[h''] at h'
            simp[←Digits.rotr_minCyc_comm] at h'
            apply Digits.len.ε_unique
            have h0:Digits.heads (Digits.not_ε_minCyc_not_ε (Digits.not_ε_append (Digits.noConfusion:ε::(0) ≠ ε) x): Digits.minCyc ( ε :: (0) ++ x) ≠ ε ) =L ε:=by rw[h]; simp
            apply λ h => Digits.len.eq.trans h h0
            apply Digits.heads_len_congr
            rw[h'', ←Digits.rotr_minCyc_comm]
            exact (Digits.rotr_len_eq _).symm
          }
          simp[h2]
          rw[Digits.minCyc_head_eq_head (Digits.not_ε_append Digits.noConfusion _)]
          simp[Digits.head_of_head_append_tails]
          simp[Digits.rotl_minCyc_comm]
          have h'':(ε::(0) ++ x).rotl = x::(0):=by{
            rw[Digits.rotl]
            simp[Digits.not_ε_append (Digits.noConfusion:ε::(0) ≠ ε) x]
            simp[Digits.tails_of_head_append_tails, Digits.head_of_head_append_tails]
          }
          simp[h'']
          have h5:((i + int.One).toStdInt - int.One).toStdInt = i.toStdInt:=by{
            rw[←int.eq_iff_toStdInt_eq]
            rw[int.sub]
            apply (int.add_congr (int.toStdInt_eq _) (int.eq.refl _)).trans
            apply (int.add.assoc _ _ _).trans
            exact int.add_zero _ (int.add_neg_eq_zero _)
          }
          rw[h5]
          rw[movl]
          simp[h0, h1]
        }
      }
    }
    | (1) => {
      have h0{d:Digit}(h:d ≠ (0)):(a::d).toStdNat ≠ ε:=by{
        intro h'
        have h':=Digits.toStdNat_ε_isZero h'
        simp[Digits.isZero] at h'
        exact h h'.right
      }
      simp[h0 _]
      simp[h']
      rw[movl]
      cases Decidable.em (Digits.heads (Digits.not_ε_minCyc_not_ε (Digits.not_ε_append (Digits.noConfusion:ε::(1) ≠ ε) x)) = ε) with
      | inl h1 => {
        simp[h1]
        have h2:Digits.tail (Digits.not_ε_minCyc_not_ε (Digits.not_ε_append (Digits.noConfusion:ε::(1) ≠ ε) x)) = (1):=by{
          have h2:(ε::(1) ++ x).minCyc = ε::(1):=by{
            have h2:ε::(1) ++ x = (x::(1)).rotr:=by simp[Digits.rotr]
            rw[h2]
            rw[←Digits.rotr_minCyc_comm]
            have h3:ε::(1) = (ε::(1)).rotr:=by simp[Digits.rotr]
            rw[h3]
            apply congrArg Digits.rotr
            rw[←Digits.eq_heads_cons_tail (Digits.not_ε_minCyc_not_ε (Digits.noConfusion:x::(1) ≠ ε))]
            simp
            apply And.intro
            . {
              apply Digits.len.ε_unique
              rw[←congrArg (λ x:Digits => _ =L x) h1]
              apply Digits.heads_len_congr (Digits.not_ε_minCyc_not_ε Digits.noConfusion) (Digits.not_ε_minCyc_not_ε (Digits.not_ε_append (Digits.noConfusion:ε::(1) ≠ ε) x))
              rw[h2, ←Digits.rotr_minCyc_comm]
              exact (Digits.rotr_len_eq _).symm
            }
            . {
              exact Digits.minCyc_tail_eq_tail Digits.noConfusion
            }
          }
          simp[h2]
          simp[Digits.tail]
        }
        simp[h2]
        rw[movr]
        simp[Digits.minCyc_tail_eq_tail (Digits.noConfusion:x::(1) ≠ ε)]
        simp[Digits.toStdNat_cons_not_zero_step]
        simp[Digits.tail, Digits.heads]
        simp[h]
        rw[Digits.rotr_minCyc_comm]
        simp[Digits.rotr]
        apply int.eq_iff_toStdInt_eq.mp
        apply (int.add_congr (int.toStdInt_eq i) (int.eq.refl _)).trans
        exact (int.toStdInt_eq _).symm
      }
      | inr h1 => {
        simp[h1]
        have h2:Digits.head (Digits.not_ε_minCyc_not_ε (Digits.not_ε_append (Digits.noConfusion:ε::(1) ≠ ε) x):(ε::(1)++x).minCyc ≠ ε) = (1):=by{
          rw[Digits.minCyc_head_eq_head (Digits.not_ε_append (Digits.noConfusion:ε::(1) ≠ ε) x)]
          rw[Digits.head_of_head_append_tails]
        }
        simp[h2]
        rw[movr]
        simp[h0 _]
        simp[Digits.minCyc_tail_eq_tail (Digits.noConfusion:x::(1) ≠ ε)]
        simp[Digits.toStdNat_cons_not_zero_step]
        simp[Digits.tail, Digits.heads]
        simp[h]
        rw[Digits.rotr_minCyc_comm]
        simp[Digits.rotr]
        apply int.eq_iff_toStdInt_eq.mp
        apply (int.add_congr (int.toStdInt_eq i) (int.eq.refl _)).trans
        exact (int.toStdInt_eq _).symm
      }
    }
    | (2) => {
      have h0{d:Digit}(h:d ≠ (0)):(a::d).toStdNat ≠ ε:=by{
        intro h'
        have h':=Digits.toStdNat_ε_isZero h'
        simp[Digits.isZero] at h'
        exact h h'.right
      }
      simp[h0 _]
      simp[h']
      rw[movl]
      cases Decidable.em (Digits.heads (Digits.not_ε_minCyc_not_ε (Digits.not_ε_append (Digits.noConfusion:ε::(2) ≠ ε) x)) = ε) with
      | inl h1 => {
        simp[h1]
        have h2:Digits.tail (Digits.not_ε_minCyc_not_ε (Digits.not_ε_append (Digits.noConfusion:ε::(2) ≠ ε) x)) = (2):=by{
          have h2:(ε::(2) ++ x).minCyc = ε::(2):=by{
            have h2:ε::(2) ++ x = (x::(2)).rotr:=by simp[Digits.rotr]
            rw[h2]
            rw[←Digits.rotr_minCyc_comm]
            have h3:ε::(2) = (ε::(2)).rotr:=by simp[Digits.rotr]
            rw[h3]
            apply congrArg Digits.rotr
            rw[←Digits.eq_heads_cons_tail (Digits.not_ε_minCyc_not_ε (Digits.noConfusion:x::(2) ≠ ε))]
            simp
            apply And.intro
            . {
              apply Digits.len.ε_unique
              rw[←congrArg (λ x:Digits => _ =L x) h1]
              apply Digits.heads_len_congr (Digits.not_ε_minCyc_not_ε Digits.noConfusion) (Digits.not_ε_minCyc_not_ε (Digits.not_ε_append (Digits.noConfusion:ε::(2) ≠ ε) x))
              rw[h2, ←Digits.rotr_minCyc_comm]
              exact (Digits.rotr_len_eq _).symm
            }
            . {
              exact Digits.minCyc_tail_eq_tail Digits.noConfusion
            }
          }
          simp[h2]
          simp[Digits.tail]
        }
        simp[h2]
        rw[movr]
        simp[Digits.minCyc_tail_eq_tail (Digits.noConfusion:x::(2) ≠ ε)]
        simp[Digits.toStdNat_cons_not_zero_step]
        simp[Digits.tail, Digits.heads]
        simp[h]
        rw[Digits.rotr_minCyc_comm]
        simp[Digits.rotr]
        apply int.eq_iff_toStdInt_eq.mp
        apply (int.add_congr (int.toStdInt_eq i) (int.eq.refl _)).trans
        exact (int.toStdInt_eq _).symm
      }
      | inr h1 => {
        simp[h1]
        have h2:Digits.head (Digits.not_ε_minCyc_not_ε (Digits.not_ε_append (Digits.noConfusion:ε::(2) ≠ ε) x):(ε::(2)++x).minCyc ≠ ε) = (2):=by{
          rw[Digits.minCyc_head_eq_head (Digits.not_ε_append (Digits.noConfusion:ε::(2) ≠ ε) x)]
          rw[Digits.head_of_head_append_tails]
        }
        simp[h2]
        rw[movr]
        simp[h0 _]
        simp[Digits.minCyc_tail_eq_tail (Digits.noConfusion:x::(2) ≠ ε)]
        simp[Digits.toStdNat_cons_not_zero_step]
        simp[Digits.tail, Digits.heads]
        simp[h]
        rw[Digits.rotr_minCyc_comm]
        simp[Digits.rotr]
        apply int.eq_iff_toStdInt_eq.mp
        apply (int.add_congr (int.toStdInt_eq i) (int.eq.refl _)).trans
        exact (int.toStdInt_eq _).symm
      }
    }
  }
  | inr h => {
    simp[h]
    have h'':(a::d).toStdNat ≠ ε:=by{
      intro h''
      apply h
      rw[←Digits.isZero_iff_toStdNat_ε] at *
      rw[Digits.isZero] at h''
      exact h''.left
    }
    simp[h'']
    have h''':=Digits.toStdNat_not_ε_cons_step h d
    simp[h''']
    rw[movr]
    simp[Digits.minCyc_tail_eq_tail]
    simp[h']
    simp[Digits.tail]
    simp[Digits.heads]
    simp[h]
    have h0:(i.toStdInt + int.One).toStdInt = (i + int.One).toStdInt:=by{
      apply int.eq_iff_toStdInt_eq.mp
      exact int.add_congr (int.toStdInt_eq i) (int.eq.refl _)
    }
    simp[h0]
    simp[Digits.rotr_minCyc_comm]
  }
}

theorem eq.movl_eq{d:Digit}{a x:Digits}{i:int}:⟨a::d, x::d, i - int.One, Digits.noConfusion⟩ =C ⟨a, (ε::d)++x, i, Digits.not_ε_append Digits.noConfusion x⟩:=by{
  apply (movr_eq _ _ _ _).trans
  apply refl' (Digits.nat.eq.refl _) (Eq.refl _)
  rw[int.sub]
  apply (int.add.assoc _ _ _).trans
  have h'':(-int.One + int.One).isZero:=by simp[int.One, int.neg, int.add, Digits.sub, Digits.half_sub, Digits.half_sub', Digit.half_sub3, int.isZero]
  exact int.add_zero i h''
}

@[inline] instance instDecidableEq{x y:cyc}:Decidable (x = y):=by{
  match x, y with
  | ⟨x0, x1, x2, _⟩, ⟨y0, y1, y2, _⟩ => {
    simp
    exact instDecidableAnd
  }
}

@[inline] instance eq.instDecidable{x y:cyc}:Decidable (x =C y):=
  instDecidableEq

theorem movl_std_props{x:Digits}(hn:x ≠ ε)(hc:x.minCyc = x)(e:int):(movl hn hc e).pre = ε ∧ (movl hn hc e).pre.isStdNat ∧ (movl hn hc e).post.minCyc = (movl hn hc e).post ∧ (movl hn hc e).exp.toStdInt = (movl hn hc e).exp:=by{
  rw[movl]
  cases Decidable.em (Digits.heads hn = ε) with
  | inl h0 => {
    simp[h0]
    cases Decidable.em (Digits.tail hn = (0)) with
    | inl h1 => {
      simp[h1]
      match x with
      | x'::d => {
        simp[Digits.heads, Digits.tail] at *
        simp[h0, h1] at hc
        exact ⟨by simp[Digits.isStdNat], hc⟩
      }
    }
    | inr h1 => {
      simp[h1]
      rw[int.toStdInt.idemp]
      exact ⟨by simp[Digits.isStdNat], hc, rfl⟩
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
      exact movl_std_props hn' hc' (e - int.One).toStdInt
    }
    | inr h1 => {
      simp[h1]
      rw[int.toStdInt.idemp]
      exact ⟨by simp[Digits.isStdNat], hc, rfl⟩
    }
  }
}
termination_by' {
  rel:=λ x y:(_:Digits) ×' _ => Digits.headzerocountLt x.fst y.fst
  wf:=InvImage.wf (λ x:(_:Digits) ×' _ => x.fst) Digits.headzerocountLt.wf
}

theorem movl_not_ε_zero_post_not_ε_zero{x:Digits}(hn:x ≠ ε)(hc:x.minCyc = x)(e:int)(he:x ≠ ε::(0)):(movl hn hc e).post ≠ ε::(0):=by{
  rw[movl]
  cases Decidable.em (Digits.heads hn = ε) with
  | inl h => {
    simp[h]
    cases Decidable.em (Digits.tail hn = (0)) with
    | inl h' => {
      match x with
      | x'::d' => {
        simp[Digits.heads, Digits.tail] at *
        simp[h, h'] at he
      }
    }
    | inr h' => {
      simp[h']
      match x with
      | x'::d' => {
        simp[Digits.tail] at h'
        simp[h']
      }
    }
  }
  | inr h => {
    simp[h]
    cases Decidable.em (Digits.head hn = (0)) with
    | inl h' => {
      simp[h']
      have hc':x.rotl.minCyc = x.rotl:=Digits.minCyc_rotl_minCyc hc
      have hn':x.rotl ≠ ε:=by{
        intro tmp
        have tmp:=Digits.rotl_cancel (tmp.trans (rfl:ε = (ε).rotl):_ = (ε).rotl)
        exact hn tmp
      }
      have he':x.rotl ≠ ε::(0):=by{
        intro hf
        apply he
        rw[←Digits.rotl_rotr_cancel x]
        rw[hf]
        simp[Digits.rotr]
      }
      have : Digits.headzerocountLt (x.rotl) x:=by{
        have : x.rotl.headzerocount.Succ =N x.headzerocount:=by{
          simp[Digits.rotl] at *
          apply Digits.nat.eq.symm
          rw[Digits.headzerocount]
          simp[hn,h']
          rw[Digits.Succ, Digits.Succ]
          apply λ h => Digits.nat.eq_of_eq_add_eq h (Digits.nat.eq.refl Digits.One)
          have tmp : ¬(Digits.tails hn).isZero:=by {
            match x with | x'::d' => {
              simp[Digits.heads] at h
              simp at hc'
              intro hf
              have tmp : ¬ x'.isZero:=by{
                rw[←Digits.tails.cons_tails h] at hf
                rw[Digits.isZero] at hf
                simp[hf.right] at *
                rw[Digits.tails.cons_tails Digits.noConfusion] at hc'
                have h'':(Digits.tails (Digits.noConfusion:(x'::(0))::(0) ≠ ε)).isZero:=by{
                  rw[←Digits.tails.cons_tails]
                  rw[←Digits.tails.cons_tails h]
                  simp[Digits.isZero]
                  exact hf
                }
                rw[h'] at hc'
                have h''':(Digits.tails (Digits.noConfusion:(x'::(0))::(0) ≠ ε)) = ε ∨ (Digits.tails (Digits.noConfusion:(x'::(0))::(0) ≠ ε)) = ε::(0) := Digits.isZero_minCyc_eq_self h'' hc'
                rw[←Digits.tails.cons_tails Digits.noConfusion] at h'''
                simp at h'''
                rw[←Digits.tails.cons_tails h] at h'''
                contradiction
              }
              apply tmp
              have h':Digits.head h = (0):=by{
                rw[Digits.head.cons_head]
                exact h'
              }
              have h'':=Digits.eq_head_append_tails h
              rw[←h'', h']
              have h':(ε::(0)).isZero:=by simp
              rw[←Digits.tails.cons_tails h] at hf
              rw[Digits.isZero] at hf
              exact Digits.zero_append_zero_isZero h' hf.left
            }
          }
          rw[Digits.notZero_cons_zero_headzerocount_eq tmp]
          exact Digits.nat.eq.refl _
        }
        exact Digits.nat.lt_iff_Succ_le.mpr this.to_le
      }
      exact movl_not_ε_zero_post_not_ε_zero hn' hc' (e - int.One).toStdInt he'
    }
    | inr h' => {
      simp[h']
      exact he
    }
  }
}
termination_by' {
  rel:=λ x y:(_:Digits) ×' _ => Digits.headzerocountLt x.fst y.fst
  wf:=InvImage.wf (λ x:(_:Digits) ×' _ => x.fst) Digits.headzerocountLt.wf
}

theorem movl_post_ε_zero_cyc_ε_zero{x:Digits}(hn:x ≠ ε)(hc:x.minCyc = x)(e:int)(hz:(movl hn hc e).post = ε::(0)):x = ε::(0):=by{
  cases Decidable.em (x = ε::(0)) with
  | inl h => exact h
  | inr h => {
    have h:=movl_not_ε_zero_post_not_ε_zero hn hc e h
    contradiction
  }
}

theorem movl_zero_props{x:Digits}(hn:x ≠ ε)(hc:x.minCyc = x)(e:int)(hz:(movl hn hc e).post = ε::(0)):(movl hn hc e).exp = int.Zero:=by{
  have hz:=movl_post_ε_zero_cyc_ε_zero hn hc e hz
  rw[movl]
  simp[hz]
  simp[Digits.heads, Digits.tail]
}

theorem movl_not_zero_props{x:Digits}(hn:x ≠ ε)(hc:x.minCyc = x)(e:int):(movl hn hc e).post = ε::(0) ∨ Digits.head (movl hn hc e).inv ≠ (0):=by{
  rw[movl]
  cases Decidable.em (Digits.heads hn = ε) with
  | inl h0 => {
    simp[h0]
    cases Decidable.em (Digits.tail hn = (0)) with
    | inl h1 => {
      simp[h1]
    }
    | inr h1 => {
      simp[h1]
      match x with
      | x'::d' => {
        simp[Digits.heads, Digits.tail] at h0 h1
        simp[h0, h1, Digits.head]
      }
    }
  }
  | inr h => {
    simp[h]
    cases Decidable.em (Digits.head hn = (0)) with
    | inl h' => {
      simp[h']
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
          simp[hn,h']
          rw[Digits.Succ, Digits.Succ]
          apply λ h => Digits.nat.eq_of_eq_add_eq h (Digits.nat.eq.refl Digits.One)
          have tmp : ¬(Digits.tails hn).isZero:=by {
            match x with | x'::d' => {
              simp[Digits.heads] at h
              simp at hc'
              intro hf
              have tmp : ¬ x'.isZero:=by{
                rw[←Digits.tails.cons_tails h] at hf
                rw[Digits.isZero] at hf
                simp[hf.right] at *
                rw[Digits.tails.cons_tails Digits.noConfusion] at hc'
                have h'':(Digits.tails (Digits.noConfusion:(x'::(0))::(0) ≠ ε)).isZero:=by{
                  rw[←Digits.tails.cons_tails]
                  rw[←Digits.tails.cons_tails h]
                  simp[Digits.isZero]
                  exact hf
                }
                rw[h'] at hc'
                have h''':(Digits.tails (Digits.noConfusion:(x'::(0))::(0) ≠ ε)) = ε ∨ (Digits.tails (Digits.noConfusion:(x'::(0))::(0) ≠ ε)) = ε::(0) := Digits.isZero_minCyc_eq_self h'' hc'
                rw[←Digits.tails.cons_tails Digits.noConfusion] at h'''
                simp at h'''
                rw[←Digits.tails.cons_tails h] at h'''
                contradiction
              }
              apply tmp
              have h':Digits.head h = (0):=by{
                rw[Digits.head.cons_head]
                exact h'
              }
              have h'':=Digits.eq_head_append_tails h
              rw[←h'', h']
              have h':(ε::(0)).isZero:=by simp
              rw[←Digits.tails.cons_tails h] at hf
              rw[Digits.isZero] at hf
              exact Digits.zero_append_zero_isZero h' hf.left
            }
          }
          rw[Digits.notZero_cons_zero_headzerocount_eq tmp]
          exact Digits.nat.eq.refl _
        }
        exact Digits.nat.lt_iff_Succ_le.mpr this.to_le
      }
      exact movl_not_zero_props hn' hc' (e - int.One).toStdInt
    }
    | inr h1 => {
      simp[h1]
    }
  }
}
termination_by' {
  rel:=λ x y:(_:Digits) ×' _ => Digits.headzerocountLt x.fst y.fst
  wf:=InvImage.wf (λ x:(_:Digits) ×' _ => x.fst) Digits.headzerocountLt.wf
}

theorem movr_std_props{n x:Digits}(hd:n.isStdNat)(hn:n ≠ ε)(hx:x ≠ ε)(hc:x.minCyc = x)(e:int):(movr hd hn hx hc e).pre.isStdNat ∧ (movr hd hn hx hc e).post.minCyc = (movr hd hn hx hc e).post ∧ (movr hd hn hx hc e).exp.toStdInt = (movr hd hn hx hc e).exp:=by{
  rw[movr]
  cases Decidable.em (Digits.tail hn = Digits.tail hx) with
  | inl h0 => {
    simp[h0]
    cases Decidable.em (Digits.heads hn = ε) with
    | inl h1 => {
      simp[h1]
      exact ⟨by{simp[Digits.isStdNat]},Digits.minCyc_rotr_minCyc hc,by{rw[int.toStdInt.idemp]}⟩
    }
    | inr h1 => {
      simp[h1]
      have h2:x.rotr ≠ ε:=by{rw[Digits.rotr_iff_rotr', Digits.rotr'];simp[hx];exact Digits.not_ε_append Digits.noConfusion _}
      have : (Digits.heads hn) <L n:=by{
        match n with
        | _::_ => simp[Digits.heads]; exact Digits.len.lt_cons _ _
      }
      exact movr_std_props (Digits.isStdNat_heads_isStdNat hn hd) h1 h2 (Digits.minCyc_rotr_minCyc hc) (e + int.One).toStdInt
    }
  }
  | inr h0 => {
    simp[h0]
    exact ⟨hd, hc, by{rw[int.toStdInt.idemp]}⟩
  }
}
termination_by' {
  rel:=λ x y => x.fst <L y.fst
  wf:=InvImage.wf (λ x:(_:Digits) ×' _ => x.fst) Digits.len.lt.wf
}

theorem movr_min_props{n x:Digits}(hd:n.isStdNat)(hn:n ≠ ε)(hx:x ≠ ε)(hc:x.minCyc = x)(e:int)(hi:(movr hd hn hx hc e).pre ≠ ε):Digits.tail hi ≠ Digits.tail (movr hd hn hx hc e).inv:=by{
  cases Decidable.em (Digits.tail hn = Digits.tail hx) with
  | inl h0 => {
    rw[movr] at hi
    simp[h0]
    cases Decidable.em (Digits.heads hn = ε) with
    | inl h1 => {
      simp[h1] at hi
      simp[h0] at hi
    }
    | inr h1 => {
      simp[h1] at hi
      have : (Digits.heads hn) <L n:=by{
        match n with
        | _::_ => simp[Digits.heads]; exact Digits.len.lt_cons _ _
      }
      simp[h0] at hi
      have h2:x.rotr ≠ ε:=by{rw[Digits.rotr_iff_rotr', Digits.rotr'];simp[hx];exact Digits.not_ε_append Digits.noConfusion _}
      have : (Digits.heads hn) <L n:=by{
        match n with
        | _::_ => simp[Digits.heads]; exact Digits.len.lt_cons _ _
      }
      have ih:=movr_min_props (Digits.isStdNat_heads_isStdNat hn hd) h1 h2 (Digits.minCyc_rotr_minCyc hc) (e + int.One).toStdInt hi
      have h3:movr hd hn hx hc e = movr (Digits.isStdNat_heads_isStdNat hn hd) h1 h2 (Digits.minCyc_rotr_minCyc hc) (e + int.One).toStdInt:=by{
        rw[movr]
        simp[h0, h1]
      }
      simp[h3]
      exact ih
    }
  }
  | inr h0 => {
    have h1:movr hd hn hx hc e = ⟨n, x, e.toStdInt, hx⟩:=by{
      rw[movr]
      simp[h0]
    }
    simp[h1]
    exact h0
  }
}
termination_by' {
  rel:=λ x y => x.fst <L y.fst
  wf:=InvImage.wf (λ x:(_:Digits) ×' _ => x.fst) Digits.len.lt.wf
}

theorem toStdCyc_std_props(c:cyc):c.toStdCyc.pre.isStdNat ∧ c.toStdCyc.post.minCyc = c.toStdCyc.post ∧ c.toStdCyc.exp.toStdInt = c.toStdCyc.exp:=by{
  match c with
  | ⟨n, x, e, h⟩ => {
    simp[toStdCyc]
    have hn: x.minCyc ≠ ε := Digits.not_ε_minCyc_not_ε h
    have hc: (x.minCyc).minCyc = x.minCyc := Digits.minCyc.idemp x
    cases Decidable.em (n.toStdNat = ε) with
    | inl h' => {
      simp[h']
      exact (movl_std_props hn hc e.toStdInt).right
    }
    | inr h' => {
      simp[h']
      exact movr_std_props (Digits.toStdNat_isStdNat n) h' hn hc e.toStdInt
    }
  }
}

theorem movr_not_zero_prop{n x:Digits}(hd:n.isStdNat)(hn:n ≠ ε)(hx:x ≠ ε)(hc:x.minCyc = x)(e:int):(movr hd hn hx hc e).pre ≠ ε ∨ Digits.head (movr hd hn hx hc e).inv ≠ (0) := by{
  rw[movr]
  cases Decidable.em (Digits.tail hn = Digits.tail hx) with
  | inl h0 => {
    simp[h0]
    cases Decidable.em (Digits.heads hn = ε) with
    | inl h1 => {
      simp[h1]
      have h2:Digits.tail hn ≠ (0):=by{
        intro h
        match n with
        | n'::d' => {
          simp[Digits.tail, Digits.heads] at *
          simp[h, h1] at hd
          simp[Digits.isStdNat] at hd
        }
      }
      intro h
      rw[←Digits.tail_eq_rotr_head hx] at h
      exact h2 (h0.trans h)
    }
    | inr h1 => {
      simp[h1]
      have h2:x.rotr ≠ ε:=by{rw[Digits.rotr_iff_rotr', Digits.rotr'];simp[hx];exact Digits.not_ε_append Digits.noConfusion _}
      have : (Digits.heads hn) <L n:=by{
        match n with
        | _::_ => simp[Digits.heads]; exact Digits.len.lt_cons _ _
      }
      exact movr_not_zero_prop (Digits.isStdNat_heads_isStdNat hn hd) h1 h2 (Digits.minCyc_rotr_minCyc hc) (e + int.One).toStdInt
    }
  }
  | inr h0 => {
    simp[h0]
    exact Or.inl hn
  }
}
termination_by' {
  rel:=λ x y => x.fst <L y.fst
  wf:=InvImage.wf (λ x:(_:Digits) ×' _ => x.fst) Digits.len.lt.wf
}

theorem toStdCyc_zero_props(c:cyc)(hn:c.toStdCyc.pre = ε)(hx:c.toStdCyc.post = ε::(0)):c.toStdCyc.exp = int.Zero:=by{
  match c with
  | ⟨n, x, e, h⟩ => {
    simp[toStdCyc] at *
    have hn': x.minCyc ≠ ε := Digits.not_ε_minCyc_not_ε h
    have hc': (x.minCyc).minCyc = x.minCyc := Digits.minCyc.idemp x
    cases Decidable.em (n.toStdNat = ε) with
    | inl h' => {
      simp[h'] at *
      exact movl_zero_props hn' hc' e.toStdInt hx
    }
    | inr h' => {
      simp[h'] at hn hx
      cases movr_not_zero_prop (Digits.toStdNat_isStdNat n) h' hn' hc' e.toStdInt with
      | inl h => contradiction
      | inr h => {
        simp[hx] at h
        contradiction
      }
    }
  }
}

theorem toStdCyc_min_props{c:cyc}(hn:c.toStdCyc.pre ≠ ε):Digits.tail hn ≠ Digits.tail c.toStdCyc.inv:=by{
  match c with
  | ⟨n,x,e,hx⟩ => {
    simp[toStdCyc] at hn
    have hn': x.minCyc ≠ ε := Digits.not_ε_minCyc_not_ε hx
    have hc': (x.minCyc).minCyc = x.minCyc := Digits.minCyc.idemp x
    cases Decidable.em (n.toStdNat = ε) with
    | inl h => {
      simp[h] at hn
      rw[(movl_std_props hn' hc' e.toStdInt).left] at hn
      contradiction
    }
    | inr h => {
      simp[h] at hn
      have hn0:=movr_min_props (Digits.toStdNat_isStdNat n) h hn' hc' e.toStdInt hn
      simp[toStdCyc]
      simp[h]
      exact hn0
    }
  }
}

theorem toStdCyc_not_zero_props(c:cyc):c.toStdCyc.pre ≠ ε ∨ c.toStdCyc.post = ε::(0) ∨ Digits.head c.toStdCyc.inv ≠ (0):=by{
  match c with
  | ⟨n, x, e, hx⟩ => {
    simp[toStdCyc]
    have hn': x.minCyc ≠ ε := Digits.not_ε_minCyc_not_ε hx
    have hc': (x.minCyc).minCyc = x.minCyc := Digits.minCyc.idemp x
    cases Decidable.em (n.toStdNat = ε) with
    | inl h => {
      simp[h]
      simp[movl_std_props]
      exact movl_not_zero_props hn' hc' e.toStdInt
    }
    | inr h => {
      simp[h]
      have h':=movr_not_zero_prop (Digits.toStdNat_isStdNat n) h hn' hc' e.toStdInt
      cases h' with
      | inl h' => {
        simp[h']
      }
      | inr h' => {
        simp[h']
      }
    }
  }
}

theorem toStdCyc.idemp(c:cyc):c.toStdCyc.toStdCyc = c.toStdCyc:=by{
  have h0:=toStdCyc_std_props c
  have h1:(hn:c.toStdCyc.pre ≠ ε) → Digits.tail hn ≠ Digits.tail c.toStdCyc.inv:=toStdCyc_min_props
  match h2:c.toStdCyc with
  | ⟨n, x, e, h⟩ => {
    simp[h2] at h0
    simp[toStdCyc]
    rw[h2] at h1
    simp[Digits.stdNat_toStdNat_eq h0.left]
    cases Decidable.em (n = ε) with
    | inl h' => {
      simp[h']
      rw[movl]
      simp[h0]
      cases Decidable.em (Digits.heads h = ε) with
      | inl h'' => {
        simp[h'']
        cases Decidable.em (Digits.tail h = (0)) with
        | inl h''' => {
          simp[h''']
          match x with
          | x'::d' => {
            simp[Digits.heads, Digits.tail] at *
            simp[h', h'', h'''] at *
            have h3:=toStdCyc_zero_props c
            simp[h2] at h3
            exact h3.symm
          }
        }
        | inr h''' => {
          simp[h''']
        }
      }
      | inr h'' => {
        simp[h'']
        cases Decidable.em (Digits.head h = (0)) with
        | inl h''' => {
          match toStdCyc_not_zero_props c with
          | Or.inl h3 => {
            simp[h2, h'] at h3
          }
          | Or.inr (Or.inl h3) => {
            simp[h2] at h3
            simp[h3] at h''
            simp[Digits.heads] at h''
          }
          | Or.inr (Or.inr h3) => {
            simp[h2] at h3
            simp[h'''] at h3
          }
        }
        | inr h''' => {
          simp[h''']
        }
      }
    }
    | inr h' => {
      simp[h']
      have h1:=h1 h'
      rw[movr]
      simp[h1, h0]
    }
  }
}

end cyc
end wkmath
