import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.WellFounded
import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Function.Basic
open Classical

section Section1_1
/-
  デデキント切断
  実数の部分集合 A B に対して
  A ≠ ∅, B ≠ ∅,
  A ∩ B = ∅
  A ∪ B = ℝ
  ∀ a ∈ A , ∀ b ∈ B, a < b
  なるものが存在する
-/
def DedekindCut (A B: Set ℝ) :=
  A.Nonempty ∧ B.Nonempty ∧ (A ∩ B = ∅) ∧ (A ∪ B = Set.univ) ∧ (∀ a ∈ A, ∀ b ∈ B, a < b)

/-
  連続性の公理
  実数の任意の切断に対して必ず次の二つのうちの必ずどちらか一方が成り立つ
  (1). Aに最大数が存在し、Bには最小数が存在しない
  (2). Aに最大数が存在せず、Bには最小数が存在する
-/
--最大数 / 最小数を持つこととは何かを定義しておく
def HasMaxElement (A: Set ℝ) :=
  ∃ x ∈ A, (∀ y ∈ A, y ≤ x)

def HasMinElement (A : Set ℝ) :=
  ∃ x ∈ A, (∀ y ∈ A , x ≤ y)

def MinElement (A : Set ℝ) (a : ℝ) :=
  a ∈ A → ∀y ∈ A , a ≤ y
--連続性の公理
axiom ContinuityAxiom {A B : Set ℝ} :
  DedekindCut A B → (HasMaxElement A ∨ HasMinElement B)

/-
上界と下界の定義
-/
/-
  上界
  A : 実数の部分集合
  b : 実数

  Aに含まれる任意の要素 a が b よりも小さい時、 bを上界という。
-/
def UpperBound (A : Set ℝ) (b : ℝ) :=
  ∀ a ∈ A, a ≤ b

/-上界の集合-/
def UpperBoundSet (A : Set ℝ) :=
  {x : ℝ | UpperBound A x}
/-
  上に有界
  与えられた集合Aの上界の条件を満たす実数が存在する
-/
def BoundedAbove
 (A : Set ℝ) :=
  ∃ x, UpperBound A x

/-
  上限
  A : 実数の部分集合

  上界の集合の最小元を上限という。
-/
def Supremum (A : Set ℝ) (x : ℝ):=
  UpperBound A x ∧  ∀ y, UpperBound A y → x ≤ y

/-
  下界
  A : 実数の部分集合
  b : 実数

  Aに含まれる任意の要素 a が b よりも大きい時、 bを下界という。
-/
def LowerBound (A : Set ℝ) (b : ℝ) :=
  ∀ a ∈ A, a ≥ b

/-
  下に有界
  与えられた集合A に対して下界の条件を満たす実数が存在する。
-/
def BoundedBelow(A : Set ℝ) :=
  ∃x, LowerBound A x

/-
有界
上にかつ下に有界
すなわち絶対値の値が上に有界
-/
def Bounded (A : Set ℝ) :=
  ∃x, (∀a ∈ A, |a| ≤ x)
/-
  下限
  A : 実数の部分集合
  x : 実数

  下界の集合の最大限を下限という
-/
def Infimum (A : Set ℝ) (x : ℝ) :=
  LowerBound A x ∧ ∀ y, LowerBound A y → y ≤ x


/-
上限の存在
空でなく上に有界なℝの部分集合は上限を持つ
-/
/-
教科書と証明手順をそろえるためのlemma
-/
lemma dedekind_comm (A B C D E : Prop):  B ∧ C ∧ D ∧ A ∧ E →  A ∧ B ∧ C ∧ D ∧ E:= by
  intro k
  rw [and_comm,and_assoc,and_assoc,and_assoc]
  rw [← and_assoc,← and_assoc, ← and_assoc,and_right_comm,and_assoc,and_assoc,and_assoc]
  exact k
/-
ある実数が上界ならばそれより大きい実数も上界
-/
lemma le_of_UpperBound (S : Set ℝ) (a : ℝ) (ub : UpperBound S a):
  ∀s ≥ a, UpperBound S s := by
    intro s sgea b binS
    have : b ≤ a := by
      apply ub;exact binS
    exact le_trans this sgea

theorem ExistSupremum:
   ∀S : Set ℝ, ((Set.Nonempty S ∧ BoundedAbove  S) → ∃a, Supremum S a):= by
  -- ⭐️ C ⊂ ℝ を上に有界な空でない集合としよう。
  intro C ⟨CnotEmpty,CBoundedAbove⟩
  -- ⭐️ BをCの上界全体の集合とすると
  let B : Set ℝ := {x : ℝ | UpperBound C x}
  -- ⭐️ 仮定よりBは空ではない。
  have BnotEmpty : B.Nonempty := CBoundedAbove
  -- ⭐️ Bの補集合R ∖B をAとする
  let A : Set ℝ := Set.univ \ B
  -- ⭐️ (A,B)が実数の切断になる
  have : DedekindCut A B := by
    apply dedekind_comm
    repeat (any_goals apply And.intro)
    . exact BnotEmpty
    . exact Set.diff_inter_self
    . rw [Set.diff_union_self,Set.univ_union]
    . let ⟨c,cinC⟩ := CnotEmpty
      have h1 : {z : ℝ | z < c}.Nonempty := by
        apply Exists.intro (c - 1)
        simp
      let ⟨z,zltc⟩ := h1
      have : z ∈ A := by
        have znotUpperBoundC : ¬ UpperBound C z := by
          rw [UpperBound]; push_neg
          apply Exists.intro
          exact ⟨cinC,zltc⟩
        exact ⟨Set.mem_univ z, znotUpperBoundC⟩
      have : A ≠ ∅ := by
        apply Set.nonempty_iff_ne_empty.1
        exact ⟨z, this⟩
      rw [Set.nonempty_iff_ne_empty]
      exact this
    . have : ∀ (a : ℝ), a ∈ A → ∀ (b : ℝ), b ∈ B → a < b := by
        intro a ainA b binB
        by_contra ageb
        push_neg at ageb
        have bUpperBoundC : UpperBound C b := binB
        have aUpperBoundC : UpperBound C a := le_of_UpperBound C b bUpperBoundC a ageb
        have ainACapB : a ∈ A ∩ B := ⟨ainA,aUpperBoundC⟩
        have ACapBnotEmp : (A ∩ B)≠ ∅ := by
          apply Set.nonempty_iff_ne_empty.1
          exact ⟨a, ainACapB⟩
        have ACapBemp : A ∩ B = ∅ := Set.diff_inter_self
        contradiction
      exact this
  have continuity : HasMaxElement A ∨ HasMinElement B := ContinuityAxiom this
  -- Bに最小数が存在すればその最小数がCの上限となる
  have : HasMinElement B → ∃x, Supremum C x := by
    intro ⟨x,h⟩
    apply Exists.intro
    exact h
  -- Aに最大数xが存在するとして矛盾が出ればよい
  suffices h : HasMaxElement A → ∃x, Supremum C x by
    exact Or.elim continuity h this
  intro AhasMaxElement
  let ⟨x,xinA,maxelem⟩ := AhasMaxElement
  have xnotInB : ¬ x ∈ B := by
    rw [Set.mem_diff] at xinA
    exact xinA.right
  have : ∃ c ∈ C, x < c := by
    have : ¬UpperBound C x := by assumption
    rw [UpperBound] at this
    push_neg at this
    exact this
  let ⟨c,cinC,xltc⟩ := this
  have : ∀z, (x < z ∧ z < c → z ∈ A):= by
    intro z ⟨_, zltc⟩
    have : ¬ UpperBound C z := by
      rw [UpperBound]
      push_neg
      exact ⟨c, cinC, zltc⟩
    exact ⟨Set.mem_univ z, this⟩
  have zemp: {z : ℝ | x < z ∧ z < c}.Nonempty := by
    apply Exists.intro ((x + c) / 2)
    apply And.intro
    . apply (lt_div_iff (by norm_num)).2
      rw [← one_add_one_eq_two,mul_add,mul_one]
      exact add_lt_add_left xltc x
    . apply (div_lt_iff (by norm_num)).2
      rw [← one_add_one_eq_two,mul_add,mul_one]
      exact add_lt_add_right xltc c
  let ⟨z, zltgt⟩ := zemp
  have : ¬ (∀ y ∈ A, y ≤ x) := by
    push_neg
    apply Exists.intro z
    exact ⟨this z zltgt,zltgt.left⟩
  contradiction

theorem ExistInfimum (C : Set ℝ) (CnotEmpty : C.Nonempty) (CBelow : BoundedBelow C):
  ∃x, Infimum C x := by
    let ⟨c,cinC⟩ := CnotEmpty
    let B : Set ℝ := {x : ℝ | LowerBound C x}
    let A : Set ℝ := Set.univ \ B
    have Dedekind : DedekindCut B A := by
      repeat (any_goals apply And.intro)
      . exact CBelow
      . let S : Set ℝ := {z : ℝ | c < z}
        have : S.Nonempty := by
          apply Exists.intro (c + 1)
          rw [Set.mem_setOf]
          simp
        let ⟨z,zinS⟩ := this
        have cltz : c < z := zinS
        have zinA : z ∈ A := by
          have : ¬ LowerBound C z := by
            rw [LowerBound]
            push_neg
            exact ⟨c, cinC, cltz⟩
          exact ⟨Set.mem_univ z, this⟩
        exact ⟨z, zinA⟩
      . rw [Set.inter_comm]
        exact Set.diff_inter_self
      . rw [Set.union_comm, Set.diff_union_self,Set.univ_union]
      . intro b binB a ainA
        by_contra neblta
        push_neg at neblta
        have : LowerBound C a := by
          intro k kinC
          have : k ≥ b := binB k kinC
          apply ge_trans this neblta
        have : a ∈ A ∩ B := ⟨ainA, this⟩
        have : a ∉ A ∩ B := by
          intro h'
          have : A ∩ B = ∅ := Set.diff_inter_self
          rw [this] at h'
          contradiction
        contradiction
    let Continuous := ContinuityAxiom Dedekind
    rcases Continuous with h | h
    . let ⟨x,⟨xinB,h1⟩⟩ := h
      apply Exists.intro x
      apply And.intro
      . exact xinB
      . exact h1
    . let ⟨x ,⟨xinA,h1⟩⟩ := h
      have : ¬ x ∈ B := by
        exact Set.not_mem_of_mem_diff xinA
      have : ∃ c ∈ C, c < x := by
        have : ¬ LowerBound C x := by exact this
        rw [LowerBound] at this; push_neg at this
        apply this
      let ⟨c,⟨cinC,cltx⟩⟩ := this
      let z : ℝ := (x + c) / 2
      have : c < z ∧ z < x := by
        apply And.intro
        . apply (lt_div_iff (by norm_num)).2
          rw [← one_add_one_eq_two,mul_add,mul_one]
          apply add_lt_add_right
          exact cltx
        . apply (div_lt_iff (by norm_num)).2
          rw [← one_add_one_eq_two,mul_add,mul_one]
          apply add_lt_add_left
          exact cltx
      have zinA : z ∈ A := by
        have : ¬ LowerBound C z := by
          rw [LowerBound]
          push_neg
          exact ⟨c, cinC, this.left⟩
        exact ⟨Set.mem_univ z, this⟩
      have : x ≤ z := h1 z zinA
      linarith

-- 上限を取り出す関数
noncomputable instance : SupSet ℝ :=
    ⟨fun A =>if h : A.Nonempty ∧ BoundedAbove A  then Classical.choose (ExistSupremum A ⟨ h.1, h.2⟩ ) else -1⟩
theorem sup (A : Set ℝ) :
  sSup A = if h : A.Nonempty ∧ BoundedAbove A then Classical.choose (ExistSupremum A ⟨ h.1, h.2⟩ ) else -1 := rfl

-- sSup S が上限になっていることを示す。
theorem Sup_def (S : Set ℝ) (SnotEmpty : S.Nonempty) (SBA : BoundedAbove S) :
  Supremum S (sSup S) := by
    simp only [sup, dif_pos (And.intro SnotEmpty SBA)]
    apply Classical.choose_spec
--上界の唯一性
theorem SupUnique (S : Set ℝ) {a b : ℝ}: Supremum S a → Supremum S b → a = b := by
  intro aSup bSup
  rw [Supremum] at *
  have aleb: a ≤ b := aSup.right b bSup.left
  have blea: b ≤ a := bSup.right a aSup.left
  apply le_antisymm aleb blea

-- Supremum と sSupの同値性
theorem Sup_sSup_iff {S : Set ℝ} (SnotEmpty : S.Nonempty) (SBA : BoundedAbove S)(a₀ : ℝ) :
  (Supremum S a₀) ↔ (sSup S = a₀) := by
    apply Iff.intro
    . intro h1
      have h2 := Sup_def S SnotEmpty SBA
      apply SupUnique S h2 h1
    . intro h1
      rw [← h1]
      exact Sup_def S SnotEmpty SBA

/-
上に有界な空でない集合 A : Set ℝ 、a₀ ∈ ℝとするとき次は同値
(1) : a₀ = sup A
(2) : a₀ はAの上界で、任意のε>0に対して A の元 a で a₀ - ε < aを満たすものがある
-/
theorem SupEquivalence {A : Set ℝ} (AnotEmpty : A.Nonempty) (ABoundAbove : BoundedAbove A) (a₀ : ℝ) :
  (sSup A = a₀) ↔ (UpperBound A a₀ ∧ ∀ε > 0, ∃ a ∈ A, a₀ - ε < a) := by
    -- ⭐️ (1) => (2)
    have left : (sSup A = a₀) → (UpperBound A a₀ ∧ ∀ε > 0, ∃ a ∈ A, a₀ - ε < a) := by
      -- a₀がAの上限であれば、
      intro ssup
      -- 書きやすい形に書き換える
      have ssup := (Sup_sSup_iff AnotEmpty ABoundAbove a₀).2 ssup
      -- ⭐️ (2)の前半はもちろん成り立っているので、
      have lleft : UpperBound A a₀ := ssup.left
      -- ⭐️ 後半だけ示せばよい。
      suffices lright : ∀ε > 0, ∃a ∈ A, a₀ - ε < a by
        exact ⟨lleft,lright⟩
      -- ⭐️ もし(2)の後半が成り立っていないと、
      by_contra h; push_neg at h
      -- ⭐️ある ε > 0に対して a₀ - ε がAの上界になってしまうので、
      have : ∃ε > 0, UpperBound A (a₀ - ε) := by
        let ⟨ε, εpos,h2⟩ := h
        apply Exists.intro ε
        apply And.intro
        . exact εpos
        . intro k kinA
          exact h2 k kinA
      let ⟨ε,εpos,h3⟩ := this
      -- ⭐️ a₀がAの最小上界である
      have a₀MinUBA:= ssup.right (a₀ - ε) h3
      -- ⭐️ という仮定に反する
      linarith
    -- ⭐️ (2) => (1)
    have right :  (UpperBound A a₀ ∧ ∀ε > 0, ∃ a ∈ A, a₀ - ε < a) → (sSup A = a₀) := by
      -- ⭐️ a₀が(2)の条件を満たしているとき、
      intro h1
      -- Aの任意の上界xに対して a₀ ≤ xであることを言えばよい。
      suffices h : ∀x, (UpperBound A x → a₀ ≤ x) by
        exact (Sup_sSup_iff AnotEmpty ABoundAbove a₀).1 ⟨h1.left,h⟩
      intro x ub
      -- ⭐️ もし a₀ ≤ x でないとすると、
      by_contra h2; push_neg at h2
      -- ⭐️ ε := a₀ - x
      let ε := a₀ - x
      -- ⭐️ >0 となり
      have εpos : ε > 0 := by
        rw [gt_iff_lt,sub_pos]; exact h2
      -- ⭐️ (2) より x = a₀ - ε
      have : x = a₀ - ε := by ring
      -- ⭐️ < a なる a ∈ A が存在する
      have : ∃a ∈ A, x < a := by
        let ⟨a,ainA,p⟩ := (h1.right ε εpos)
        rw [this]
        exact ⟨a, ainA, p⟩
      -- ⭐️ ことになり、
      let ⟨a,ainA,xlta⟩ := this
      -- ⭐️ x が Aの上界であること
      have := ub a ainA
      -- ⭐️ に矛盾する。
      linarith
    exact Iff.intro left right
--下限を取り出す
noncomputable instance : InfSet ℝ :=
  ⟨fun A => if h : A.Nonempty ∧ BoundedBelow A then Classical.choose (ExistInfimum A h.1 h.2) else -1⟩
theorem inf (A : Set ℝ) :
  sInf A = if h : A.Nonempty ∧ BoundedBelow A then Classical.choose (ExistInfimum A h.1 h.2) else -1 := rfl

--sInf が下限になっていることをしめす
theorem Inf_def (S : Set ℝ) (SnotEmpty : S.Nonempty) (SBB : BoundedBelow S) :
  Infimum S (sInf S) := by
    simp only [inf,dif_pos (And.intro SnotEmpty SBB)]
    apply Classical.choose_spec
--下限の同一性
theorem InfUnique {S : Set ℝ} {a b : ℝ}: Infimum S a → Infimum S b → a = b := by
  intro aInf bInf
  rw [Infimum] at *
  apply le_antisymm (bInf.right a aInf.left) (aInf.right b bInf.left)
-- InfimumとsInfの同値性
theorem Inf_sInf_iff {S : Set ℝ} (SnotEmpty : S.Nonempty) (SBB : BoundedBelow S) {a : ℝ}:
  (Infimum S a) ↔ (sInf S = a) := by
    apply Iff.intro
    . intro h1
      have h2 := Inf_def S SnotEmpty SBB
      apply InfUnique h2 h1
    . intro h1
      rw [← h1]
      apply Inf_def S SnotEmpty SBB

--すべての下界は下限よりも小さい
lemma Inf_LowerBound {S : Set ℝ} (SnotEmpty : S.Nonempty) (SBB : BoundedBelow S):
  ∀ s, LowerBound S s → s ≤ sInf S := by
    intro s LB
    have := Inf_def S SnotEmpty SBB
    rw [Infimum] at this
    apply this.right s LB
-- 集合の要素は下限よりも大きい
lemma Element_ge_Inf {S : Set ℝ} (SnotEmpty : S.Nonempty) (SBB : BoundedBelow S) :
  ∀ s ∈ S, s ≥ sInf S := by
    intro s sinS
    have := (Inf_def S SnotEmpty SBB).left
    exact this s sinS
/-
下に有界な空でない集合 A : Set ℝ 、a₀ ∈ ℝとするとき次は同値
(1) : a₀ = inf A
(2) : a₀ はAの下界で、任意のε>0に対して A の元 a で a < a₀ + ε を満たすものがある
-/
theorem InfEpsLemma (A : Set ℝ) (AnotEmpty : A.Nonempty) (ABoundedBelow : BoundedBelow A) (a₀ : ℝ) :
   (sInf A = a₀) ↔ (LowerBound A a₀ ∧ ∀ε > 0, ∃ a ∈ A,a < a₀ + ε) := by
    apply Iff.intro
    . -- (1) -> (2)
      --仮定を導入し、下限を書き換える
      intro sinf
      have a₀InfA := Inf_def A AnotEmpty ABoundedBelow
      rw [sinf] at a₀InfA
      rw [Infimum] at a₀InfA
      --結論の論理積の左右をそれぞれ証明していく
      apply And.intro
      . --これは下限の定義から自明
        apply a₀InfA.left
      . --結論が偽であると仮定して矛盾することを示す
        by_contra h
        --否定を中に入れる
        push_neg at h
        --ε を固定する。
        let ⟨ε,⟨εpos,h1⟩⟩ := h
        --この時、a₀ + ε が A　の下界になってしまう。ところが、a₀は最大下界であるから矛盾する。
        --まず、a₀ + εを z とおき、それがAの下界であることを示す。
        have : LowerBound A (a₀ + ε) := by
          rw [LowerBound]
          apply h1
        --これにより a₀ ≤ a₀ + εが出てくる
        have : (a₀ + ε) ≤ a₀ := a₀InfA.right (a₀ + ε) this
        --整理すると ε ≤ 0 が出てくる
        simp at this
        --矛盾発生。 linarith tacticsを使う
        linarith
    . -- (2) -> (1)
      --仮定を導入しておく
      intro ⟨a₀LowerBoundA, h⟩
      --Infimumを書き換え
      apply (Inf_sInf_iff AnotEmpty ABoundedBelow).1
      rw [Infimum]
      --任意のAの下界x に対して  x ≤ a₀ であることを言えばいい。
      --leanでの場合は結論の後者
      apply And.intro
      . exact a₀LowerBoundA
      . --ここからが教科書の証明。
        --∀ をx で固定し、それがAの下界であると仮定する。
        intro x xLowerBoundA
        --x ≤ a₀ でないと仮定する
        by_contra a₀lex
        --否定を中に入れる
        push_neg at a₀lex
        --εを x - a₀ に固定する。
        let ε : ℝ := x - a₀
        --正であることを示す
        have a₀negxpos : ε  > 0 := by
          simp only [ε]
          rw [gt_iff_lt, sub_pos]
          exact a₀lex
        -- これを上限の定義の部分に代入する
        have h1 := h ε a₀negxpos
        simp at h1
        -- x が A の下界であることと矛盾することを示す
        rw [LowerBound] at xLowerBoundA
        -- a　を固定
        let ⟨a,⟨ainA, altx⟩⟩ := h1
        --このa を Aの下界の定義に適用すると a ≥ xが出てくる
        have : a ≥ x := xLowerBoundA a ainA
        --これによりxがAの上界であることについて矛盾が発生。
        simp [ε] at altx
        linarith
lemma InfPositiveEqualZero : sInf {x : ℝ | x > 0} = 0:= by
  -- ⭐️ この証明では P :={x : ℝ | x > 0}とする。
  let P : Set ℝ := {x : ℝ | x > 0}
  -- P が空でないことと下に有界であることを使うためあらかじめ言っておく
  have PnotEmpty : P.Nonempty := by
    have : 1 ∈ P := by
      rw [Set.mem_setOf]
      norm_num
    exact ⟨1, this⟩
  -- ⭐️ 定義により 0 はP の下界であるから
  have LB: LowerBound P 0 := by
    intro a h1
    exact le_of_lt h1
  have PBB : BoundedBelow P := by
    exact ⟨0, LB⟩
  -- ⭐️ inf P ≥ 0 である。
  have gezero: sInf P ≥ 0 := Inf_LowerBound PnotEmpty PBB 0 LB
  -- ⭐️ もしも inf P > 0 であったとすると、
  have negtzero: ¬sInf P > 0 := by
    intro gtzero
    -- ⭐️ (1 /2) inf P ∈ P だから
    have : (1 / 2) * (sInf P) ∈ P := by
      rw [Set.mem_setOf_eq,gt_iff_lt,div_mul_comm,mul_one]
      apply (lt_div_iff (by norm_num)).2
      rw [zero_mul]
      exact gtzero
    -- ⭐️ (1 /2) inf P ≥ inf P でなければならない。
    have : (1 /2) * (sInf P) ≥ (sInf P) := Element_ge_Inf PnotEmpty PBB ((1 /2) * (sInf P)) this
    -- ⭐️これより inf P ≤ 0 となり、
    rw [ge_iff_le,div_mul_comm,mul_one,le_div_iff (by norm_num), ← one_add_one_eq_two,mul_add,mul_one,add_le_iff_nonpos_right] at this
    -- ⭐️ inf P > 0　としたことに矛盾する。
    linarith
  push_neg at negtzero
  exact le_antisymm negtzero gezero

lemma alebByEps (a b : ℝ): (∀ε > 0, a < b + ε) → a ≤ b:= by
  intro h
    -- ⭐️ この証明では P :={x : ℝ | x > 0}とする。
  let P : Set ℝ := {x : ℝ | x > 0}
  -- P が空でないことと下に有界であることを使うためあらかじめ言っておく
  have PnotEmpty : P.Nonempty := by
    exact ⟨1, (show 1 ∈ P by rw [Set.mem_setOf]; norm_num)⟩
  -- ⭐️ 定義により 0 はP の下界であるから
  have LB: LowerBound P 0 := by
    intro a h1
    exact le_of_lt h1
  have PBB : BoundedBelow P := by
    exact ⟨0, LB⟩
  -- ⭐️ (2) の仮定は a - b が P の下界　であることを言っているので、
  have lbab : LowerBound P (a - b) := by
    intro p pinP
    have := h p pinP
    linarith
  -- ⭐️ a - b ≤ inf P = 0 となり、
  have := Inf_LowerBound PnotEmpty PBB (a - b) lbab
  have sInfzero: sInf P = 0 := InfPositiveEqualZero
  -- ⭐️ a ≤ b が成り立つ。
  have : a ≤ b := by
    rw [sInfzero,tsub_le_iff_right,zero_add] at this
    exact this
  exact this

lemma abs_eps_zero (a : ℝ):(∀ ε > 0, |a| < ε) → a = 0 := by
  intro h
  -- ⭐️ 仮定と、すでに示した (2)より、 |a| ≤ 0 が得られるので
  have abslezero : |a| ≤ 0 := by
    have := alebByEps |a| 0
    -- このままだと絶対値までsimpされてしまうのでそれはやらないようにする
    -- [- theorem]でsimpで用いるtheoremから[]内のものを除くことが可能
    simp[- abs_nonpos_iff] at this
    exact this h
  -- ⭐️ a = 0 である。
  have : a = 0 := by
    rw [abs_nonpos_iff] at abslezero
    exact abslezero
  exact this

  /-
  Archimedesの原理
  a, b > 0 とするととある自然数 n に対して n * a > b が成り立つ
  leanの自然数と教科書の自然数の定義でずれがあるので(n + 1) * a > bに修正した
-/
theorem ArchimedesPrinciple : ∀a > 0, ∀ b > 0, (∃n : ℕ, ((n + (1 : ℕ)) : ℝ) * a > b) := by
  --　仮定を導入
  intro a apos b _
  -- (n + 1) * a ≤ b と仮定して矛盾を導く
  by_contra! h
  -- C := { n * a | n ∈ ℕ} とする
  let C : Set ℝ:= {s : ℝ | ∃ k : ℕ, s =  ((k + (1 : ℕ)) : ℝ ) * a}
  -- あとで使うために C が空でないことを言っておく
  have CnotEmpty : C.Nonempty := by
    -- s = a, k = 0 とすれば成り立つ
    apply Exists.intro a
    apply Exists.intro 0
    rw [CharP.cast_eq_zero,Nat.cast_one,zero_add,one_mul]
  -- C が上に有界であることも言っておく
  have CUB : BoundedAbove C := by
    -- b が上界であることを使う
    have : UpperBound C b := by
      intro k kinC
      let ⟨k',k'h⟩ := kinC
      rw [k'h]
      exact h k'
    exact ⟨b, this⟩
  -- 上で示したことにより C が上限を持つことを言えた
  have CSup := ExistSupremum C ⟨CnotEmpty, CUB⟩
  -- 上限を x という変数でおく。
  let ⟨x, SupCx⟩ := CSup
  -- 任意の自然数 n に対して (n + 2) * a ≤ x であることを示す
  have : ∀n : ℕ, ((n + (2 : ℕ )) : ℝ)  * a ≤ x := by
    intro n
    -- SupCxの左側　UpperBound C x を上手く使うため、 (n + 1) * a が C の要素であることをいう
    have : ((n + (2 : ℕ )) : ℝ) * a ∈ C := by
      rw [Set.mem_setOf_eq]
      apply Exists.intro (n + 1)
      rw [Nat.cast_ofNat,Nat.cast_add,Nat.cast_one,← one_add_one_eq_two,mul_eq_mul_right_iff]
      apply Or.inl
      rw [add_assoc]
    -- 結果を素直に用いれば示せる
    apply SupCx.left ((n + 2) * a) this
  have : ∀n : ℕ, ((n + 1 : ℕ) : ℝ)* a ≤ x - a := by
    intro n
    have := this n
    rw [← one_add_one_eq_two] at this
    rw [Nat.cast_add,Nat.cast_one,← add_assoc,add_comm,add_mul,one_mul,add_comm] at this
    apply le_tsub_of_add_le_right
    rw [Nat.cast_add,Nat.cast_one]
    exact this
  -- x - a が C の上界となることをいう
  have up: UpperBound C (x - a) := by
    intro l ⟨k, kp⟩
    have := this k
    rw [kp,Nat.cast_one]
    rw [Nat.cast_add,Nat.cast_one] at this
    exact this
  have : ∀y, UpperBound C y → x ≤ y := SupCx.right
  have := this (x - a) up
  linarith

lemma OneDivnltEps : ∀ ε > (0 : ℝ) , (∃ n : ℕ , 1 / ((n + (1 : ℕ)) : ℝ) < ε)  := by
  --仮定を導入
  intro ε εpos
  --アルキメデスの定理に a = ε, b = 1 を代入
  have := ArchimedesPrinciple ε εpos (1 : ℝ) (by norm_num)
  let ⟨n, h⟩ := this
  -- n を使用
  apply Exists.intro n
  -- n + 1 > 0を先に示す
  have : ((n + (1 : ℕ)): ℝ) > 0 := by
    rw [gt_iff_lt,← Nat.cast_add,← Nat.cast_zero,Nat.cast_lt,add_pos_iff]
    right
    exact zero_lt_one
  -- nを両辺にかける。
  apply (div_lt_iff this).2
  -- 積を交換
  rw [mul_comm]
  -- h を適用して証明は終了
  exact h


theorem NatHasMinElement (S : Set ℕ):
  S.Nonempty → ∃x ∈ S,∀y ∈ S,  x ≤ y:= by
    intro SnotEmpty
    -- 最小値を持たないと仮定する
    by_contra! h
    -- 任意の自然数は S に含まれないことを示す
    have :∀ n : ℕ ,(n ∉ S) := by
      -- forall を固定
      intro n
      --数学的帰納法を用いる。
      induction' n using Nat.strong_induction_on with n ih
      intro ninS
      have := h n ninS
      let ⟨y,⟨yinS,yltn⟩⟩ := this
      have := ih y yltn
      -- 矛盾発生
      contradiction
    -- 矛盾発生
    rw [Set.Nonempty] at SnotEmpty
    let ⟨x,xinS⟩ := SnotEmpty
    have := this x
    contradiction

-- 補助定理　あとで使う
theorem sub_le_abc (a b c : ℝ) : a - b ≤ c ↔ a - b - c ≤ 0 := by
  apply Iff.intro
  . rw [tsub_le_iff_right,tsub_le_iff_right,zero_add,tsub_le_iff_right]
    intro k; exact k
  . rw [tsub_le_iff_right,tsub_le_iff_right,zero_add,tsub_le_iff_right]
    intro l; exact l

theorem sub_assoc (a b : ℝ) : -b - a = -(b + a) := by
  ring

lemma RationalnumberDenseness : ∀ x, ∀ ε > 0, (∃q : ℚ, |x - (q : ℝ)| < ε ) := by
  intro x ε εpos
  have xposh : ∀ x > 0, ∀ ε > 0, (∃q : ℚ, |x - (q : ℝ)| < ε) := by
    intro x xpos ε εpos
    -- 系　1.5 よりある自然数 n に対して 1 / n + 1 < ε なる n が存在する
    have onediv := OneDivnltEps ε εpos
    let ⟨n,h⟩ := onediv
    -- ある自然数m で m + 1 /n + 1 > x が成立する(アルキメデスの原理)
    -- 1 / n + 1 > 0 を示す
    have onedivnpos : 0 < 1 / ((n + (1 : ℕ)) : ℝ)  := by
      have : ((n + (1 : ℕ)) : ℝ)  > 0 := by
        rw [gt_iff_lt,← Nat.cast_add,← Nat.cast_zero,Nat.cast_lt,add_pos_iff]
        right
        exact zero_lt_one
      apply (lt_div_iff this).2
      rw [zero_mul]
      exact zero_lt_one
    -- アルキメデスの原理よりある 自然数 m で(m + 1)/(n + 1) > x が出てくる
    have archi:= ArchimedesPrinciple (1 /((n + (1 : ℕ)) : ℝ)) (onedivnpos) x xpos
    -- そのような条件を満たす m の集合を考える
    let M : Set ℕ := {m : ℕ | ((m + 1) : ℕ) / ((n + 1): ℕ) > x}
    -- M が空でないことをまずいう
    have MnotEmpty : M.Nonempty := by
      let ⟨m, h1⟩ := archi
      apply Exists.intro m
      rw [mul_div,mul_one,Nat.cast_one] at h1
      rw [Set.mem_setOf_eq,Nat.cast_add,Nat.cast_add,Nat.cast_one]
      exact h1
    -- よって最小元がある
    let ⟨m,⟨minM,mmin⟩⟩ := NatHasMinElement M MnotEmpty
    --その最小元を使ってqを固定する。
    let q : ℚ := ((m + 1):ℕ )  / ((n + 1):ℕ)
    apply Exists.intro q
    -- 以下は教科書では略されているがここからが大変
    -- x - q が負であることをまず示す
    have xsubqneg: x - q < 0 := by
      rw [sub_neg]
      rw [Set.mem_setOf_eq,gt_iff_lt,Nat.cast_add,Nat.cast_add,Nat.cast_one] at minM
      simp [q]
      exact minM
    -- 絶対値を外す
    rw [abs_of_neg xsubqneg]
    -- 括弧の前のマイナスを中に入れる
    rw [neg_sub]
    -- a ≤ b , b < c → a < c を使う。
    apply lt_of_le_of_lt _ h
    --しばし変形を行う x を右辺に持っていくために色々な式変形をしている
    rw [sub_le_abc,sub_eq_add_neg,sub_eq_add_neg,add_assoc,add_comm (-x),← add_assoc,← sub_eq_add_neg]
    rw [← sub_eq_add_neg,← sub_le_abc]
    -- 通分を行う。
    have h2: (q : ℝ)  - 1 / (n + (1 : ℕ)) = m / (n + (1 : ℕ)) := by
      ring_nf
      simp
      rw [add_mul,one_mul]
      simp
      rw [mul_comm]
    rw [h2]
    -- x < m / (n + 1) と仮定して矛盾を示す。
    by_contra h
    push_neg at h
    -- m ≥ 1 の場合と m < 1 の場合で場合わけを行う。 m - 1 が 自然数であるかどうかが重要
    -- 自然数は減算に関して閉じていないので場合わけを行い自然数専用のライブラリを使わないと
    -- 上手く証明することができない。扱いが難しかった。
    by_cases hm :m ≥ 1
      -- (m - 1)が M に含まれていることを示す。
    . have msubinM: (m - 1) ∈ M := by
        simp only [M, Set.mem_setOf]
        -- -1 + 1 = 0 を用いる。nat. を使わないといけない点には注意
        rw [Nat.sub_add_cancel hm]
        -- h のcastも動かすことで 結論の式と一致する
        norm_cast at h
      -- (m - 1)がMに含まれていることがわかったので m ≤ m - 1が出てくる
      have : m ≤ m - 1 := mmin (m - 1) msubinM
      -- m > m - 1を示す。
      have : m > m - 1 := by
        -- 0 < m , 0 < 1 より m - 1 < m が出てくる。
        apply Nat.sub_lt _ (by norm_num)
          -- 0 < m を示す
        . have : 0 < (1 : ℕ) := by norm_num
          -- 0 < 1, 1 ≤ m より 0 < m が出てくる
          apply lt_of_lt_of_le this hm
      -- ここまでで矛盾発生。
      linarith
    -- m < 1 のとき
    . push_neg at hm
      -- m = 0 であることをまず示す
      have : m = 0 := by
        apply Nat.lt_one_iff.1 hm
      -- m を代入
      rw [this] at h
      simp at h
      -- x > 0 と x < 0　で矛盾
      linarith
  rcases lt_trichotomy x 0 with h | h | h
  . have : -x > 0 := by simp; exact h
    let ⟨q,h1⟩ := xposh (-x) this ε εpos
    apply Exists.intro (-q)
    simp
    rw [sub_assoc,abs_neg] at h1
    exact h1
  . rw [h]
    apply Exists.intro 0
    rw [zero_sub,abs_neg]
    norm_cast
  . exact xposh x h ε εpos

end Section1_1
