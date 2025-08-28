import «LeanExportInfos».Dedekind.Main_Reconstruct_1_1

open Classical
section Section1_2

/-
ε - δ 法
x : 自然数を受けて実数を返す関数。数列の代わり
a : 収束先の値

x (n) が a に収束するとは、任意の ε>0 に対して、あるn₀が存在し、
任意の n ≥ n₀ なる n に対して |x (n) - a| < ε が成り立つことを言う。
-/
def ConvergesTo (x : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ n₀, ∀ n ≥ n₀, |x (n) - a| < ε

/-
  命題 1. 7
  極限の一意性
  実数列 {x_n}n が a,b ∈ ℝ に対して x_n → a, x_n → b ならば a = bである
-/

theorem LimitUniqueness (x : ℕ → ℝ) (a b: ℝ)
    (xlima : ConvergesTo x a) (xlimb : ConvergesTo x b) :
    a = b := by
    -- 任意のε >0 に対して |a - b| < εを示す。
    have : ∀ ε > 0, |a - b| < ε := by
      -- ⭐️ 任意に ε > 0 をとると、x_n → a かつ x_n → b から、
      intro ε εpos
      -- ⭐️ あるn₁, n₂で n ≥ n₂ → |x_n - a| < ε/2
      have n₁eps := xlima (ε / 2) (by exact half_pos εpos)
      let ⟨n₁,n₁h⟩ := n₁eps
      -- ⭐️ n ≥ n₂ → |x_n - b| < ε/2 をみたすものがある。
      have n₂eps := xlimb (ε / 2) (by exact half_pos εpos)
      let ⟨n₂,n₂h⟩ := n₂eps
      -- ⭐️ 従って n ≥ max {n₁, n₂} とすれば、
      let n := max n₁ n₂
      have : n ≥ max n₁ n₂ := by rw [ge_iff_le]
      -- ⭐️ |a - b| = |(a - x_n) + (x_n - b)| ≤ |x_n - a| + |x_n - b| < ε/2 + ε/2 = ε となる.
      calc
        |a - b| = |(a - x n) + (x n - b)| := by
          rw [add_sub,sub_add_cancel]
        _ ≤  |x n - a| + |x n - b| := by
          rw [abs_sub_comm]
          exact abs_add (a - x n) (x n - b)
        _ < ε / 2 + ε / 2 := (add_lt_add (n₁h n (le_of_max_le_left this)) (n₂h n (le_of_max_le_right this)))
        _ = ε := add_halves ε
    -- ⭐️ よって補題 1.3 により a = b が得られる。
    exact eq_of_sub_eq_zero (abs_eps_zero (a - b) this)

/-
  数列が収束するとは、その数列がある実数aに対して収束するということである。
-/
def IsConverges(x : ℕ → ℝ) :=
  ∃a, ConvergesTo x a

class Lim (α : Type*) where
  sLim : (ℕ → α) → α
noncomputable instance : Lim ℝ :=
  ⟨fun x => if h :IsConverges x then Classical.choose h else 0⟩

theorem Limit (x : ℕ → ℝ) :
  Lim.sLim x = if h :IsConverges x then Classical.choose h else 0 := rfl

theorem Limit_def (x : ℕ → ℝ) (conv : IsConverges x):
  ConvergesTo x (Lim.sLim x) :=by
    simp only [Limit,dif_pos conv]
    apply Classical.choose_spec

theorem Converges_sLim_iff (x : ℕ → ℝ) (conv : IsConverges x) (a : ℝ):
  ConvergesTo x a ↔ (Lim.sLim x = a) := by
    apply Iff.intro
    . intro h1
      have h2 := Limit_def x conv
      exact LimitUniqueness x (Lim.sLim x) a h2 h1
    . intro h1
      rw [← h1]
      exact Limit_def x (conv)

theorem Limit_add (x y : ℕ → ℝ) (conx : IsConverges x) (cony : IsConverges y):
  Lim.sLim (x + y) = Lim.sLim x + Lim.sLim y := by
    have : IsConverges (x + y) := by
      let ⟨a, convxa⟩ := conx
      let ⟨b, convyb⟩ := cony
      apply Exists.intro (a + b)
      intro ε εpos
      let ⟨n₁,h1⟩ := convxa (ε/2) (half_pos εpos)
      let ⟨n₂,h2⟩ := convyb (ε/2) (half_pos εpos)
      let n₀ := max n₁ n₂
      apply Exists.intro n₀
      intro n nlen₀
      calc
        |x n + y n - (a + b)| ≤ |x n - a| + |y n - b| := by
          rw [add_sub_add_comm]
          apply abs_add
        _ < ε / 2 + ε / 2 := by
          have : n₀ ≥ max n₁ n₂ := Nat.le_refl (max n₁ n₂)
          apply add_lt_add (h1 n (le_trans (le_of_max_le_left this) nlen₀)) (h2 n (le_trans (le_of_max_le_right this) nlen₀))
        _ = ε := add_halves' ε
    apply LimitUniqueness (x + y)
    . exact Limit_def (x + y) this
    . intro ε εpos
      let ⟨a, convxa⟩ := conx
      let ⟨b, convyb⟩ := cony
      let ⟨n₁,h1⟩ := convxa (ε/2) (half_pos εpos)
      let ⟨n₂,h2⟩ := convyb (ε/2) (half_pos εpos)
      let n₀ := max n₁ n₂
      apply Exists.intro n₀
      intro n nlen₀
      calc
        |(x + y) n - (Lim.sLim x + Lim.sLim y)| = |(x n -Lim.sLim x ) + (y n - Lim.sLim y)| := by
          rw [Pi.add_apply,add_sub_add_comm]
        _ ≤ |x n - Lim.sLim x| + |y n - Lim.sLim y| := abs_add _ _
        _ = |x n - a| + |y n - b| := by
          have h1: Lim.sLim x = a := (Converges_sLim_iff x conx a).1 convxa
          have h2: Lim.sLim y = b := (Converges_sLim_iff y cony b).1 convyb
          rw [h1, h2]
        _ < ε / 2 + ε / 2 := by
          have : n₀ ≥ max n₁ n₂ := Nat.le_refl (max n₁ n₂)
          apply add_lt_add (h1 n (le_trans (le_of_max_le_left this) nlen₀)) (h2 n (le_trans (le_of_max_le_right this) nlen₀))
        _ = ε := add_halves' ε


  theorem Limit_const_mul (x : ℕ → ℝ) (conx : IsConverges x) (α : ℝ):
    Lim.sLim (fun n => α * (x n)) = α * Lim.sLim x := by
      let ⟨a,convxa⟩ := conx
      have : IsConverges (fun n => α * (x n)) := by
          apply Exists.intro (α * a)
          intro ε εpos
          let ⟨n₀, h⟩ := convxa (ε / (|α| + 1)) (div_pos εpos (Right.add_pos_of_nonneg_of_pos (abs_nonneg α) (by norm_num)))
          apply Exists.intro n₀
          intro n nlen₀
          calc
            |α * (x n) - α * a| = |α| * |x n - a| := by
              rw [← mul_sub, abs_mul]
            _ ≤ (|α| * ε /(|α| + 1))  := by
              rw [← mul_div]
              by_cases h1 :|α| > 0
              . rw [mul_le_mul_left h1]
                apply le_of_lt
                exact h n nlen₀
              . push_neg at h1
                rw [abs_nonpos_iff] at h1
                rw [h1,abs_zero,zero_mul,zero_mul]
            _ < ε := by
              rw [mul_comm,← mul_div,mul_lt_iff_lt_one_right εpos, div_lt_iff (Right.add_pos_of_nonneg_of_pos (abs_nonneg α) (by norm_num))]
              rw [one_mul,lt_add_iff_pos_right]
              exact zero_lt_one
      apply LimitUniqueness (fun n => α * (x n))
      . exact Limit_def (fun n => α * (x n)) this
      . intro ε εpos
        let ⟨n₀, h⟩ := convxa (ε / (|α| + 1)) (div_pos εpos (Right.add_pos_of_nonneg_of_pos (abs_nonneg α) (by norm_num)))
        apply Exists.intro n₀
        intro n nlen₀
        have : Lim.sLim x = a := (Converges_sLim_iff x conx a).1 convxa
        rw [this]
        calc
          |α * (x n) - α * a| = |α| * |x n - a| := by
            rw [← mul_sub, abs_mul]
          _ ≤ (|α| * ε /(|α| + 1))  := by
            rw [← mul_div]
            by_cases h1 :|α| > 0
            . rw [mul_le_mul_left h1]
              apply le_of_lt
              exact h n nlen₀
            . push_neg at h1
              rw [abs_nonpos_iff] at h1
              rw [h1,abs_zero,zero_mul,zero_mul]
          _ < ε := by
            rw [mul_comm,← mul_div,mul_lt_iff_lt_one_right εpos, div_lt_iff (Right.add_pos_of_nonneg_of_pos (abs_nonneg α) (by norm_num))]
            rw [one_mul,lt_add_iff_pos_right]
            exact zero_lt_one

/-
  定理1.8 (1) (a)
  すべてのnで x_n = a ならば {x_n}nは収束し、 lim(n → ∞) x_n = a
-/

theorem Converges_Const (x : ℕ → ℝ) (a : ℝ) : (∀n, x n = a) → ConvergesTo x a := by
  intro xconst
  have : ∀ε > 0, ∀n, |x n - a| < ε := by
    intro ε εpos n
    have : ∀n, |x n - a| = 0 := by
      intro n
      rw [xconst n,sub_self,abs_zero]
    rw [this n]
    exact εpos
  intro ε εpos
  apply Exists.intro 1
  intro n _
  exact this ε εpos n

theorem Converges_Const' (a : ℝ) : ConvergesTo (fun _ : ℕ ↦ a) a := by
  intro ε εpos
  apply Exists.intro 1
  intro n _
  have : |(fun _ => a) n - a| = 0 := by
    rw [sub_self,abs_zero]
  rw [this]
  exact εpos

theorem Converges_Add' (x y : ℕ → ℝ) (a b : ℝ)
  (conxa : ConvergesTo x a) (conyb : ConvergesTo y b) :
    ConvergesTo (fun n ↦ x n + y n) (a + b) := by
  intro ε εpos
  let ⟨n₁,h1⟩ := conxa (ε / 2) (by apply half_pos εpos)
  let ⟨n₂,h2⟩ := conyb (ε / 2) (by apply half_pos εpos)
  let n₀ := max n₁ n₂
  apply Exists.intro n₀
  intro n nlen₀
  calc
    |x n + y n - (a + b)| ≤ |x n - a| + |y n - b| := by
      rw [add_sub_add_comm]
      apply abs_add
    _ < ε / 2 + ε / 2 := by
      have : n₀ ≥ max n₁ n₂ := Nat.le_refl (max n₁ n₂)
      apply add_lt_add (h1 n (le_trans (le_of_max_le_left this) nlen₀)) (h2 n (le_trans (le_of_max_le_right this) nlen₀))
    _ = ε := add_halves' ε
/-
  定理1.8 (1) (b)
  {x_n}n,{y_n}nが収束すれば {x_n + y_n}n も収束し、
  lim(x_n + y_n) = lim x_n + lim y_n が成り立つ
-/

theorem Converges_Add (x y : ℕ → ℝ) (conx : IsConverges x) (cony : IsConverges y) :
  Lim.sLim (x + y) = (Lim.sLim x) + (Lim.sLim y) := by
    -- ⭐️ a := lim x_n, b := lim y_n　とする。
    let ⟨a, convxa⟩ := conx
    let ⟨b, convyb⟩ := cony
    have : ConvergesTo (x + y) (a + b) := by
      -- ⭐️ このとき任意の ε > 0に対して
      intro ε εpos
      -- ⭐️ n₁, n₂ ∈ ℕ があって、
      -- ⭐️ n ≥ n₁ → |x_n - a| < ε / 2
      -- ⭐️ n ≥ n₂ → |y_n - b| < ε / 2 となる。
      let ⟨n₁,h1⟩ := convxa (ε / 2) (by apply half_pos εpos)
      let ⟨n₂,h2⟩ := convyb (ε / 2) (by apply half_pos εpos)
      -- ⭐️ n₁, n₂の大きいほうをn₀とすれば、
      let n₀ := max n₁ n₂
      -- ⭐️ n ≥ n₀ のとき
      have : ∀ n ≥ n₀, |(x n + y n) - (a + b)| < ε := by
        intro n ngen₀
        calc
          |x n + y n - (a + b)| ≤ |x n - a| + |y n - b| := by
            rw [add_sub_add_comm]
            apply abs_add
          _ < ε / 2 + ε / 2 := by
            have : n₀ ≥ max n₁ n₂ := Nat.le_refl (max n₁ n₂)
            apply add_lt_add (h1 n (le_trans (le_of_max_le_left this) ngen₀)) (h2 n (le_trans (le_of_max_le_right this) ngen₀))
          _ = ε := add_halves ε
      -- ⭐️となり、
      exact ⟨n₀, this⟩
    -- ⭐️ (b)が示された。
    exact Limit_add x y conx cony

/-
定理 1.8 (c)
{x_n}nが収束すれば {αx_n}n も収束し lim αx_n = α lim x_n が成り立つ。
-/
theorem Converges_const_mul (x : ℕ → ℝ) (α : ℝ) (conx : IsConverges x):
  Lim.sLim (fun n => α * (x n)) = α * Lim.sLim x := by
  -- ⭐️ a := lim x_n とすると、
  let ⟨a,convxa⟩ := conx
  have : ConvergesTo (fun n => α * (x n)) (α*a):= by
    -- ⭐️ 任意の ε > 0 に対して、
    intro ε εpos
    -- ⭐️ n₀ ∈ ℕ で n ≥ n₀ ならば |x_n - a| < ε / (|α| + 1)となるものが存在する
    let ⟨n₀, h⟩ := convxa (ε / (|α| + 1)) (div_pos εpos (Right.add_pos_of_nonneg_of_pos (abs_nonneg α) (by norm_num)))
    -- ⭐️ n ≥ n₀ なら
    apply Exists.intro n₀
    intro n nlen₀
    /-
      ⭐️
      |αx_n - αa| = |α||x_n - a| ≤ |α| * ε / (|α| + 1) < ε
      となるので (c)が示された.
    -/
    calc
      |α * (x n) - α * a| = |α| * |x n - a| := by
        rw [← mul_sub, abs_mul]
      _ ≤ (|α| * ε /(|α| + 1)) := by
        rw [← mul_div]
        by_cases h1 :|α| > 0
        . rw [mul_le_mul_left h1]
          apply le_of_lt
          exact h n nlen₀
        . push_neg at h1
          simp at h1
          rw [h1,abs_zero,zero_mul,zero_mul]
      _ < ε := by
        rw [mul_comm,← mul_div,mul_lt_iff_lt_one_right εpos, div_lt_iff (Right.add_pos_of_nonneg_of_pos (by simp) (by norm_num))]
        rw [one_mul]
        simp
  exact Limit_const_mul x conx α

theorem Converges_const_mul' (x : ℕ → ℝ) (α : ℝ) (a : ℝ):
  (ConvergesTo x a) → (ConvergesTo (fun n ↦ α * (x n)) (α * a)) := by
    intro convxa
    -- ⭐️ 任意の ε > 0 に対して、
    intro ε εpos
    -- ⭐️ n₀ ∈ ℕ で n ≥ n₀ ならば |x_n - a| < ε / (|α| + 1)となるものが存在する
    let ⟨n₀, h⟩ := convxa (ε / (|α| + 1)) (div_pos εpos (Right.add_pos_of_nonneg_of_pos (abs_nonneg α) (by norm_num)))
    -- ⭐️ n ≥ n₀ なら
    apply Exists.intro n₀
    intro n nlen₀
    /-
      ⭐️
      |αx_n - αa| = |α||x_n - a| ≤ |α| * ε / (|α| + 1) < ε
      となるので (c)が示された.
    -/
    calc
      |α * (x n) - α * a| = |α| * |x n - a| := by
        rw [← mul_sub, abs_mul]
      _ ≤ (|α| * ε /(|α| + 1)) := by
        rw [← mul_div]
        by_cases h1 :|α| > 0
        . rw [mul_le_mul_left h1]
          apply le_of_lt
          exact h n nlen₀
        . push_neg at h1
          simp at h1
          rw [h1,abs_zero,zero_mul,zero_mul]
      _ < ε := by
        rw [mul_comm,← mul_div,mul_lt_iff_lt_one_right εpos, div_lt_iff (Right.add_pos_of_nonneg_of_pos (by simp) (by norm_num))]
        rw [one_mul]
        simp

/-
  数列の有界性
  数列の値の集合が実数の部分集合として有界であることをいう
-/

def SequenceUpperBound (x : ℕ → ℝ) : Prop :=
  BoundedAbove {y : ℝ | ∃n : ℕ, y = x n}
def SequenceLowerBound (x : ℕ → ℝ) : Prop :=
  BoundedBelow {y : ℝ| ∃ n : ℕ, y = x n}
def SequenceBounded (x : ℕ → ℝ) :=
  BoundedAbove {y : ℝ | ∃n : ℕ, y = |x n|}
/-
  補題1.9
  収束数列は有界である。
-/
theorem ConvergentSequenceBounded:
    ∀(x : ℕ → ℝ), (IsConverges x → SequenceBounded x):= by
    -- ⭐️ {x_n}_n がaに収束する数列とする。
    intro x ⟨a, x_conv_to_a⟩
    -- ⭐️ このときε-n₀式の収束の定義で ε = 1 と考えて、
    -- ⭐️ ある n₀ ∈ ℕ でn ≥ n₀ ならば |x n - a| < 1 となるものがある。
    have := x_conv_to_a 1 (by norm_num)
    let ⟨n₀, h1⟩ := this
    -- ⭐️ これより n ≥ n₀ ならば |x_n| < |a| + 1 であるから、
    have h2: ∀n ≥ n₀, |x n| < |a| + 1 := by
      intro n ngen₀
      have h2₁ := abs_sub_abs_le_abs_sub (x n) a
      have h2₂ := h1 n ngen₀
      exact lt_add_of_tsub_lt_left (lt_of_le_of_lt h2₁ h2₂)
    -- ⭐️ M := max {|x₁|, |x₂|, ... , |a| + 1}とおけば
    let Z : Finset ℝ := (Multiset.ofList ((List.range n₀).map (|x ·|) ++ [|a| + 1])).toFinset
    have : Z.Nonempty := by
      rw [Finset.Nonempty]
      apply Exists.intro (|a| + 1)
      simp [Z]
    let ⟨M,finmax⟩ := (Finset.max_of_nonempty this)
    -- ⭐️ すべての n に対し |x_n| ≤ M が成り立ち、
    have : ∀ n, |x n| ≤ M := by
      intro n
      -- 教科書では明示されていないものの基本は場合わけで考えているはず
      by_cases h : n ≥ n₀
      . have h3 := h2 n h
        have h4 : |a| + 1 ≤ M := by
          have : (|a| + 1) ∈ Z := by simp [Z]
          have := Finset.le_max this; rw [finmax] at this
          norm_cast at this
        have := lt_of_lt_of_le h3 h4
        exact le_of_lt this
      . push_neg at h
        have :  |x n| ∈ Z := by
          simp [Z]
          left
          exact ⟨n, h, rfl⟩
        have := Finset.le_max this; rw [finmax] at this
        norm_cast at this
    -- ⭐️ {x_n}nが有界なことが示された。
    apply Exists.intro M
    intro a
    rw [Set.mem_setOf]
    intro k1
    let ⟨n,k2⟩ := k1
    rw [k2]
    exact this n

theorem Converges_mul (x y : ℕ → ℝ) (conx : IsConverges x) (cony : IsConverges y):
  Lim.sLim (x * y) = Lim.sLim x * Lim.sLim y := by
    -- ⭐️ a := lim x_n , b := lim y_n とする
    let ⟨a, convxa⟩ := conx
    let ⟨b, convyb⟩ := cony
    -- ⭐️ 次に示す補題1.9より
    -- ⭐️ ある定数M > 0に対して |x_n| ≤ M ,|y_n| ≤ M (n = 1,2,...)
    have m1h: ∃M > 0, ∀n, |x n| ≤ M := by
      let ⟨m1,h2⟩ := ConvergentSequenceBounded x conx
      -- m1 が0 の場合も考えてm1 と 1 のうち大きいほうを使う
      apply Exists.intro (max m1 1)
      rw [UpperBound] at h2
      simp at h2
      apply And.intro
      . rw [gt_iff_lt,lt_max_iff]
        right; norm_num
      . intro n
        rw [le_max_iff]
        left
        exact h2 n
    let ⟨m1,hm1⟩ := m1h
    have m2h : ∃M > 0, ∀n, |y n| ≤ M := by
      let ⟨m2,h2⟩ := ConvergentSequenceBounded y cony
      apply Exists.intro (max m2 1)
      apply And.intro
      . rw [gt_iff_lt,lt_max_iff]
        right; norm_num
      . intro n
        rw [UpperBound] at h2; simp at h2
        rw [le_max_iff]
        left
        exact h2 n
    let ⟨m2,_⟩ := m2h
    -- ⭐️ ここでMは大きいもので置き換えてよいので M ≥ |b|としてよい
    let M := max (max m1 m2) |b|
    have Mgeabsb : M ≥ |b| := le_max_right (max m1 m2) |b|
    have muleps : ∀ε > 0,∃n₀, ∀n ≥ n₀, |(x n)*(y n) - a * b| < ε := by
      intro ε εpos
      have ε2Mpos : 0 < ε / (2 * M) := by
        have Mpos : 0 < 2 * M := by
          rw [mul_pos_iff_of_pos_left (by norm_num), lt_max_iff]
          left
          rw [lt_max_iff]
          left
          exact hm1.left
        apply (lt_div_iff Mpos).2
        rw [zero_mul]; exact εpos
      -- ⭐️　あるn_0 があってn ≥ n_0 ならば |x_n-a|,|y_n-b|<ϵ/2M
      have c1 := convxa (ε / (2 * M)) ε2Mpos
      let ⟨n1,cn1⟩ := c1
      have c2 := convyb (ε / (2 * M)) ε2Mpos
      let ⟨n2,cn2⟩ := c2
      let n₀ := max n1 n2
      apply Exists.intro n₀
      intro n ngen₀
      calc
        |x n * y n - a * b| = |(x n * y n - x n * b) + (x n * b - a * b)| := by
          rw [sub_add_sub_cancel]
        _ ≤ |(x n * y n - x n * b)| + |(x n * b - a * b)| := abs_add _ _
        _ = |(x n)| * |y n - b| + |x n - a| * |b| := by
          rw [← sub_mul,← mul_sub,abs_mul,abs_mul]
        _ ≤ M * |y n - b| + M * |x n - a| := by
          have m1leM : m1 ≤ M := by
            rw [le_max_iff]
            left
            rw [le_max_iff]
            left
            exact le_refl m1
          have k1 : |x n| * |y n - b| ≤ M * |y n - b| := by
            have : |x n| ≤ M := le_trans (hm1.right n) m1leM
            exact mul_le_mul_of_nonneg_right this (abs_nonneg (y n - b))
          have k2 : |x n - a| * |b| ≤ M * |x n - a| := by
            rw [mul_comm]
            exact mul_le_mul_of_nonneg_right Mgeabsb (abs_nonneg (x n - a))
          exact add_le_add k1 k2
        _ < ε /2 + ε /2 := by
          have Mpos : 0 < M := by
            rw [lt_max_iff]; left;
            rw [lt_max_iff]; left; exact hm1.left
          have k1 :  M * |y n - b| < M * (ε/ (2 * M)) := by
            apply (mul_lt_mul_left Mpos).2
            have n0gen2 : n₀ ≥ n2 := by
              rw [ge_iff_le,le_max_iff]
              right
              exact le_refl n2
            exact cn2 n (ge_trans ngen₀ n0gen2)
          have k2 : M * |x n - a| < M * (ε/ (2 * M)) := by
            apply (mul_lt_mul_left Mpos).2
            have n0gen1 : n₀ ≥ n1 := by
              rw [ge_iff_le,le_max_iff]
              left; exact le_refl n1
            exact cn1 n (ge_trans ngen₀ n0gen1)
          have : M * (ε / (2 * M)) = ε / 2 := by
            have : M ≠ 0 := by
              exact Ne.symm (ne_of_lt Mpos)
            rw [mul_div,div_eq_inv_mul,mul_inv,← mul_assoc,mul_comm,mul_assoc,inv_mul_cancel this,mul_one,div_eq_inv_mul,mul_comm]
          rw [this] at k1 k2
          exact add_lt_add k1 k2
        _ = ε := by
          exact add_halves ε
    -- ⭐️ となり x_n y_n→ab が示された.
    have : Lim.sLim (x * y) = Lim.sLim x * Lim.sLim y := by
      apply LimitUniqueness (x * y)
      . exact Limit_def (x * y) ⟨(a * b), muleps⟩
      . intro ε εpos
        have l1 : Lim.sLim x = a := by
          exact (Converges_sLim_iff x conx a).1 convxa
        have l2 : Lim.sLim y = b := by
          exact (Converges_sLim_iff y cony b).1 convyb
        rw [l1,l2]
        exact muleps ε εpos
    exact this

theorem Converges_mul' (x y : ℕ → ℝ) (a b : ℝ):
  (ConvergesTo x a ∧ ConvergesTo y b) → ConvergesTo (fun n ↦ (x * y) n) (a * b) := by
    intro ⟨convxa, convyb⟩
    -- ⭐️ 次に示す補題1.9より
    -- ⭐️ ある定数M > 0に対して |x_n| ≤ M ,|y_n| ≤ M (n = 1,2,...)
    have m1h: ∃M > 0, ∀n, |x n| ≤ M := by
      let ⟨m1,h2⟩ := ConvergentSequenceBounded x ⟨a ,convxa⟩
      -- m1 が0 の場合も考えてm1 と 1 のうち大きいほうを使う
      apply Exists.intro (max m1 1)
      rw [UpperBound] at h2
      simp at h2
      apply And.intro
      . rw [gt_iff_lt,lt_max_iff]
        right; norm_num
      . intro n
        rw [le_max_iff]
        left
        exact h2 n
    let ⟨m1,hm1⟩ := m1h
    have m2h : ∃M > 0, ∀n, |y n| ≤ M := by
      let ⟨m2,h2⟩ := ConvergentSequenceBounded y ⟨b,convyb⟩
      apply Exists.intro (max m2 1)
      apply And.intro
      . rw [gt_iff_lt,lt_max_iff]
        right; norm_num
      . intro n
        rw [UpperBound] at h2; simp at h2
        rw [le_max_iff]
        left
        exact h2 n
    let ⟨m2,_⟩ := m2h
    -- ⭐️ ここでMは大きいもので置き換えてよいので M ≥ |b|としてよい
    let M := max (max m1 m2) |b|
    have Mgeabsb : M ≥ |b| := le_max_right (max m1 m2) |b|
    intro ε εpos
    have ε2Mpos : 0 < ε / (2 * M) := by
      have Mpos : 0 < 2 * M := by
        rw [mul_pos_iff_of_pos_left (by norm_num), lt_max_iff]
        left
        rw [lt_max_iff]
        left
        exact hm1.left
      apply (lt_div_iff Mpos).2
      rw [zero_mul]; exact εpos
    -- ⭐️　あるn_0 があってn ≥ n_0 ならば |x_n-a|,|y_n-b|<ϵ/2M
    have c1 := convxa (ε / (2 * M)) ε2Mpos
    let ⟨n1,cn1⟩ := c1
    have c2 := convyb (ε / (2 * M)) ε2Mpos
    let ⟨n2,cn2⟩ := c2
    let n₀ := max n1 n2
    apply Exists.intro n₀
    intro n ngen₀
    calc
      |x n * y n - a * b| = |(x n * y n - x n * b) + (x n * b - a * b)| := by
        rw [sub_add_sub_cancel]
      _ ≤ |(x n * y n - x n * b)| + |(x n * b - a * b)| := abs_add _ _
      _ = |(x n)| * |y n - b| + |x n - a| * |b| := by
        rw [← sub_mul,← mul_sub,abs_mul,abs_mul]
      _ ≤ M * |y n - b| + M * |x n - a| := by
        have m1leM : m1 ≤ M := by
          rw [le_max_iff]
          left
          rw [le_max_iff]
          left
          exact le_refl m1
        have k1 : |x n| * |y n - b| ≤ M * |y n - b| := by
          have : |x n| ≤ M := le_trans (hm1.right n) m1leM
          exact mul_le_mul_of_nonneg_right this (abs_nonneg (y n - b))
        have k2 : |x n - a| * |b| ≤ M * |x n - a| := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_right Mgeabsb (abs_nonneg (x n - a))
        exact add_le_add k1 k2
      _ < ε /2 + ε /2 := by
        have Mpos : 0 < M := by
          rw [lt_max_iff]; left;
          rw [lt_max_iff]; left; exact hm1.left
        have k1 :  M * |y n - b| < M * (ε/ (2 * M)) := by
          apply (mul_lt_mul_left Mpos).2
          have n0gen2 : n₀ ≥ n2 := by
            rw [ge_iff_le,le_max_iff]
            right
            exact le_refl n2
          exact cn2 n (ge_trans ngen₀ n0gen2)
        have k2 : M * |x n - a| < M * (ε/ (2 * M)) := by
          apply (mul_lt_mul_left Mpos).2
          have n0gen1 : n₀ ≥ n1 := by
            rw [ge_iff_le,le_max_iff]
            left; exact le_refl n1
          exact cn1 n (ge_trans ngen₀ n0gen1)
        have : M * (ε / (2 * M)) = ε / 2 := by
          have : M ≠ 0 := by
            exact Ne.symm (ne_of_lt Mpos)
          rw [mul_div,div_eq_inv_mul,mul_inv,← mul_assoc,mul_comm,mul_assoc,inv_mul_cancel this,mul_one,div_eq_inv_mul,mul_comm]
        rw [this] at k1 k2
        exact add_lt_add k1 k2
      _ = ε := by
        exact add_halves ε

theorem Converges_div (x y: ℕ → ℝ) (conx : IsConverges x) (cony : IsConverges y) (yneqzero : ∀n, (y n) ≠ 0):
  Lim.sLim y ≠ 0 → Lim.sLim (x / y) = Lim.sLim x / Lim.sLim y := by
    intro ylimneqzero
    suffices h1 : IsConverges (1 / y) ∧ Lim.sLim (1 / y) = 1 / (Lim.sLim y) by
      have := Converges_mul x (1 / y) conx h1.left
      rw [h1.right,mul_div,mul_one,mul_div,mul_one] at this
      exact this
    let ⟨b,convyb⟩ := cony
    have neqzero: b ≠ 0 := by
      have beqlim: Lim.sLim y = b := by
        apply LimitUniqueness y
        . exact Limit_def y cony
        . exact convyb
      rw [beqlim] at ylimneqzero
      exact ylimneqzero
    have convdiv : ConvergesTo (1 / y) (1 / b) := by
      have absbpos: |b| > 0 := by
        rw [gt_iff_lt]
        exact abs_pos.2 neqzero
      have h3: ∃n₁, ∀n ≥ n₁, |y n - b| < |b| / 2 := convyb (|b|/2) (half_pos absbpos)
      let ⟨n₁,h₁⟩ := h3
      have yngtabsb : ∀n ≥ n₁, |y n| > |b| / 2 := by
        intro n ngen₁
        have := h₁ n ngen₁
        rw [abs_sub_comm] at this
        have sub : |b| - |y n| ≤ |b - y n| := abs_sub_abs_le_abs_sub b (y n)
        have := lt_of_le_of_lt sub this
        rw [sub_lt_comm] at this
        have subhalf : |b| - |b| / 2 = |b| / 2 := by ring
        rw [subhalf] at this
        exact this
      intro ε εpos
      have h4: ∃n₂, ∀n ≥ n₂, |y n - b| < (|b| * |b| * ε / 2) := by
        have bbεpos : (|b| * |b| * ε / 2) > 0 := by
          rw [gt_iff_lt,lt_div_iff (by norm_num),zero_mul,mul_assoc]
          exact mul_pos absbpos (mul_pos absbpos εpos)
        exact convyb (|b| * |b| * ε / 2) bbεpos

      let ⟨n₂,h₂⟩ := h4
      let n₀ := max n₁ n₂
      have n₀max : max n₁ n₂ ≤ n₀ := by simp
      have h5 : ∀n ≥ n₀, |(1 / (y n)) - (1 / b)| < ε :=by
        intro n ngen₀
        calc
          |1 / y n - 1 / b| =  (1 / |(y n) * b|) * |y n - b| := by
            rw [mul_comm,mul_div,mul_one,div_eq_mul_inv,div_eq_mul_inv,div_eq_mul_inv,one_mul,one_mul]
            rw [← abs_inv,← abs_mul,sub_mul,mul_inv,← mul_assoc,mul_inv_cancel,one_mul,← mul_assoc]
            rw [mul_comm,← mul_assoc,inv_mul_cancel,one_mul,abs_sub_comm]
            exact neqzero; exact yneqzero n
          _ < (2 / (|b| * |b|)) * ((|b| * |b| * ε) / 2) := by
            have n₁len₀ : n₁ ≤ n₀ := le_of_max_le_left n₀max
            have n₂len₀ : n₂ ≤ n₀ := le_of_max_le_right n₀max
            rw [abs_mul,mul_comm,mul_div]
            have : 1 / (|y n| * |b|) < (2 / (|b| * |b|)) := by
              have := yngtabsb n (le_trans n₁len₀ ngen₀)
              have : 1 / |y n| < 2 / |b| := by
                rw [one_div]
                apply (lt_div_iff absbpos).2
                rw [mul_comm]
                have absynpos : |y n|⁻¹ > 0 := by
                  rw [gt_iff_lt,inv_pos]
                  exact abs_pos.2 (yneqzero n)
                apply (lt_div_iff absynpos).1
                rw [div_eq_mul_inv,inv_inv,mul_comm]
                rw [gt_iff_lt, div_lt_iff (by norm_num)] at this
                exact this
              rw [one_div,mul_inv,← one_div,div_eq_mul_one_div 2,one_div (|b| * |b|),mul_inv,← mul_assoc]
              rw [← one_div,mul_div 2,mul_one]
              have divabsbpos : 1 / |b| > 0 :=by
                rw [one_div,gt_iff_lt,inv_pos]
                exact absbpos
              exact (mul_lt_mul_right divabsbpos).2 this
            rw [← mul_div,mul_comm]
            have l1: 2 / (|b| * |b|) > 0 := by
              rw [gt_iff_lt]
              have absbpow : |b| * |b| > 0 := Real.mul_pos absbpos absbpos
              apply (lt_div_iff absbpow).2
              rw [zero_mul]
              norm_num
            exact mul_lt_mul_of_le_of_le' (le_of_lt this) (h₂ n (le_trans n₂len₀ ngen₀)) l1 (abs_nonneg (y n - b))
          _ = ε := by
            ring_nf
            rw [← one_add_one_eq_two,pow_add,pow_one,pow_add,pow_one,← mul_assoc,← abs_inv,← abs_mul,← abs_mul,mul_assoc b, abs_mul,mul_inv_cancel]
            rw [abs_one,mul_one,← abs_mul,mul_inv_cancel,abs_one,one_mul]
            repeat (any_goals exact neqzero)
      apply Exists.intro n₀
      exact h5
    . apply And.intro
      . exact ⟨(1 / b), convdiv⟩
      . have l1:= (Converges_sLim_iff (1 / y) ⟨(1 / b), convdiv⟩ (1 / b)).1 convdiv
        have l2:= (Converges_sLim_iff y cony b).1 convyb
        rw [l2.symm] at l1
        exact l1

theorem Converges_div'(x y : ℕ → ℝ) (a b : ℝ) (bnotzero : b ≠ 0) (yneqzero : ∀n, (y n) ≠ 0):
  (ConvergesTo x a ∧ ConvergesTo y b) → ConvergesTo (fun n ↦ (x / y) n) (a / b):= by
    intro ⟨convxa, convyb⟩
    suffices h1 : ConvergesTo (fun n ↦ 1 / (y n)) (1 / b) by
      have := Converges_mul' x (1 / y) a (1 / b) ⟨convxa,h1⟩
      rw [mul_div,mul_one,mul_div,mul_one] at this
      exact this
    have absbpos: |b| > 0 := by
      rw [gt_iff_lt]
      exact abs_pos.2 bnotzero
    have h3: ∃n₁, ∀n ≥ n₁, |y n - b| < |b| / 2 := convyb (|b|/2) (half_pos absbpos)
    let ⟨n₁,h₁⟩ := h3
    have yngtabsb : ∀n ≥ n₁, |y n| > |b| / 2 := by
      intro n ngen₁
      have := h₁ n ngen₁
      rw [abs_sub_comm] at this
      have sub : |b| - |y n| ≤ |b - y n| := abs_sub_abs_le_abs_sub b (y n)
      have := lt_of_le_of_lt sub this
      rw [sub_lt_comm] at this
      have subhalf : |b| - |b| / 2 = |b| / 2 := by ring
      rw [subhalf] at this
      exact this
    intro ε εpos
    have h4: ∃n₂, ∀n ≥ n₂, |y n - b| < (|b| * |b| * ε / 2) := by
      have bbεpos : (|b| * |b| * ε / 2) > 0 := by
        rw [gt_iff_lt,lt_div_iff (by norm_num),zero_mul,mul_assoc]
        exact mul_pos absbpos (mul_pos absbpos εpos)
      exact convyb (|b| * |b| * ε / 2) bbεpos
    let ⟨n₂,h₂⟩ := h4
    let n₀ := max n₁ n₂
    have n₀max : max n₁ n₂ ≤ n₀ := by simp
    apply Exists.intro n₀
    intro n ngen₀
    calc
      |1 / y n - 1 / b| =  (1 / |(y n) * b|) * |y n - b| := by
        rw [mul_comm,mul_div,mul_one,div_eq_mul_inv,div_eq_mul_inv,div_eq_mul_inv,one_mul,one_mul]
        rw [← abs_inv,← abs_mul,sub_mul,mul_inv,← mul_assoc,mul_inv_cancel,one_mul,← mul_assoc]
        rw [mul_comm,← mul_assoc,inv_mul_cancel,one_mul,abs_sub_comm]
        exact bnotzero; exact yneqzero n
      _ < (2 / (|b| * |b|)) * ((|b| * |b| * ε) / 2) := by
        have n₁len₀ : n₁ ≤ n₀ := le_of_max_le_left n₀max
        have n₂len₀ : n₂ ≤ n₀ := le_of_max_le_right n₀max
        rw [abs_mul,mul_comm,mul_div]
        have : 1 / (|y n| * |b|) < (2 / (|b| * |b|)) := by
          have := yngtabsb n (le_trans n₁len₀ ngen₀)
          have : 1 / |y n| < 2 / |b| := by
            rw [one_div]
            apply (lt_div_iff absbpos).2
            rw [mul_comm]
            have absynpos : |y n|⁻¹ > 0 := by
              rw [gt_iff_lt,inv_pos]
              exact abs_pos.2 (yneqzero n)
            apply (lt_div_iff absynpos).1
            rw [div_eq_mul_inv,inv_inv,mul_comm]
            rw [gt_iff_lt, div_lt_iff (by norm_num)] at this
            exact this
          rw [one_div,mul_inv,← one_div,div_eq_mul_one_div 2,one_div (|b| * |b|),mul_inv,← mul_assoc]
          rw [← one_div,mul_div 2,mul_one]
          have divabsbpos : 1 / |b| > 0 :=by
            rw [one_div,gt_iff_lt,inv_pos]
            exact absbpos
          exact (mul_lt_mul_right divabsbpos).2 this
        rw [← mul_div,mul_comm]
        have l1: 2 / (|b| * |b|) > 0 := by
          rw [gt_iff_lt]
          have absbpow : |b| * |b| > 0 := Real.mul_pos absbpos absbpos
          apply (lt_div_iff absbpow).2
          rw [zero_mul]
          norm_num
        exact mul_lt_mul_of_le_of_le' (le_of_lt this) (h₂ n (le_trans n₂len₀ ngen₀)) l1 (abs_nonneg (y n - b))
      _ = ε := by
        ring_nf
        rw [← one_add_one_eq_two,pow_add,pow_one,pow_add,pow_one,← mul_assoc,← abs_inv,← abs_mul,← abs_mul,mul_assoc b, abs_mul,mul_inv_cancel]
        rw [abs_one,mul_one,← abs_mul,mul_inv_cancel,abs_one,one_mul]
        repeat (any_goals exact bnotzero)

/-
  命題1.8 (2) (a)
  {x_n }_n,{y_n }_n が収束し, すべてのn でx_n≤y_n ならば lim⁡〖x_n 〗≤lim⁡y_n が成り立つ.
-/
theorem Converges_Le (x y : ℕ → ℝ) (convx : IsConverges x) (convy : IsConverges y):
  (∀ n, x n ≤ y n) → Lim.sLim x ≤ Lim.sLim y := by
    intro xnleyn
    -- ⭐️ a∶=lim⁡〖x_n 〗,b∶=lim⁡y_n とする.
    let ⟨a,convxa⟩ := convx
    let ⟨b,convyb⟩ := convy
    have : ∀ε > 0, a < b + ε := by
      -- ⭐️ 任意のε > 0 に対して
      intro ε εpos
      -- ⭐️ n_1,n_2∈N があって, n≥n_1→|x_n-a|<ϵ/2,n≥n_2→|y_n-b|<ϵ/2
      let ⟨n₁,h1⟩ := convxa (ε / 2) (half_pos εpos)
      let ⟨n₂,h2⟩ := convyb (ε / 2) (half_pos εpos)
      -- ⭐️ n_1,n_2 の大きいほうをn_0 とすれば
      let n₀ := max n₁ n₂
      -- ⭐️ n ≥n_0 のとき a-ϵ/2< x_n≤y_n< b+ϵ/2
      have between : ∀n ≥ n₀, a - (ε / 2) < x n ∧ x n ≤ y n ∧ y n < b + (ε / 2) := by
        intro n ngen₀
        have n₀gen₁ : n₀ ≥ n₁ := Nat.le_max_left n₁ n₂
        have n₀gen₂ : n₀ ≥ n₂ := Nat.le_max_right n₁ n₂
        repeat (any_goals apply And.intro)
        . have := (h1 n (ge_trans ngen₀ n₀gen₁))
          rw [abs_lt, lt_tsub_iff_left] at this
          exact this.left
        . exact xnleyn n
        . have := h2 n (ge_trans ngen₀ n₀gen₂)
          rw [abs_lt] at this
          have := this.right
          apply lt_add_of_neg_add_lt_left
          rw [add_comm]
          exact this
      -- ⭐️ なのでa< b+ϵ となる.
      have := between n₀ (le_refl n₀)
      have aepsltbeps : a - ε /2 < b + ε / 2 := lt_trans (lt_of_lt_of_le this.left this.right.left) this.right.right
      rw [← add_halves ε,← add_assoc,add_comm]
      apply lt_add_of_neg_add_lt_left
      rw [add_comm]
      exact aepsltbeps
    -- ⭐️ ϵ>0 は任意だったので, これから a≤b が分かる(補題1.3参照)
    have aleb : a ≤ b := alebByEps a b this
    rw [(Converges_sLim_iff x convx a).1 convxa, (Converges_sLim_iff y convy b).1 convyb]
    exact aleb

theorem Converges_Le' (x y : ℕ → ℝ) (a b : ℝ)(convx : ConvergesTo x a) (convy : ConvergesTo y b):
  (∀ n, x n ≤ y n) → a ≤ b := by
    intro xnleyn
    -- ⭐️ a∶=lim⁡〖x_n 〗,b∶=lim⁡y_n とする.
    have : ∀ε > 0, a < b + ε := by
      -- ⭐️ 任意のε > 0 に対して
      intro ε εpos
      -- ⭐️ n_1,n_2∈N があって, n≥n_1→|x_n-a|<ϵ/2,n≥n_2→|y_n-b|<ϵ/2
      let ⟨n₁,h1⟩ := convx (ε / 2) (half_pos εpos)
      let ⟨n₂,h2⟩ := convy (ε / 2) (half_pos εpos)
      -- ⭐️ n_1,n_2 の大きいほうをn_0 とすれば
      let n₀ := max n₁ n₂
      -- ⭐️ n ≥n_0 のとき a-ϵ/2< x_n≤y_n< b+ϵ/2
      have between : ∀n ≥ n₀, a - (ε / 2) < x n ∧ x n ≤ y n ∧ y n < b + (ε / 2) := by
        intro n ngen₀
        have n₀gen₁ : n₀ ≥ n₁ := Nat.le_max_left n₁ n₂
        have n₀gen₂ : n₀ ≥ n₂ := Nat.le_max_right n₁ n₂
        repeat (any_goals apply And.intro)
        . have := (h1 n (ge_trans ngen₀ n₀gen₁))
          rw [abs_lt, lt_tsub_iff_left] at this
          exact this.left
        . exact xnleyn n
        . have := h2 n (ge_trans ngen₀ n₀gen₂)
          rw [abs_lt] at this
          have := this.right
          apply lt_add_of_neg_add_lt_left
          rw [add_comm]
          exact this
      -- ⭐️ なのでa< b+ϵ となる.
      have := between n₀ (le_refl n₀)
      have aepsltbeps : a - ε /2 < b + ε / 2 := lt_trans (lt_of_lt_of_le this.left this.right.left) this.right.right
      rw [← add_halves ε,← add_assoc,add_comm]
      apply lt_add_of_neg_add_lt_left
      rw [add_comm]
      exact aepsltbeps
    -- ⭐️ ϵ>0 は任意だったので, これから a≤b が分かる(補題1.3参照)
    exact alebByEps a b this
/-
すべてのn でx_n≤aならばlim⁡〖x_n 〗≤a
-/
theorem Converges_le_const (x : ℕ → ℝ) (a : ℝ) (convx : IsConverges x) :
  (∀ n, x n ≤ a) → Lim.sLim x ≤ a := by
    intro xnlea
    let y :ℕ → ℝ := (fun _ => a)
    have xnleyn : ∀n, x n ≤ y n := by
      intro n
      exact xnlea n
    have convya : ConvergesTo y a := Converges_Const y a (fun n => rfl)
    have convy : IsConverges y := ⟨a, convya⟩
    have := Converges_Le x y convx convy xnleyn
    rw [← (Converges_sLim_iff y convy a).1 convya]
    exact this
theorem Converges_le_const' (x : ℕ → ℝ) (a b: ℝ) (convx : ConvergesTo x a) :
  (∀ n, x n ≤ b) → a ≤ b := by
    intro xnleb
    let y :ℕ → ℝ := (fun _ => b)
    have xnleyn : ∀n, x n ≤ y n := by
      intro n
      exact xnleb n
    have convyb : ConvergesTo y b := Converges_Const y b (fun n => rfl)
    exact Converges_Le' x y a b convx convyb xnleyn

/-
すべてのn でx_n ≥ aならばlim⁡〖x_n 〗≥ a
-/
theorem Converges_ge_const (x : ℕ → ℝ) (a : ℝ) (convx : IsConverges x) :
  (∀ n, x n ≥ a) → Lim.sLim x ≥ a := by
    intro xngea
    let y : ℕ → ℝ := (fun _ => a)
    have ynlexn : ∀n, y n ≤ x n := by
      intro n
      exact xngea n
    have convya : ConvergesTo y a := (Converges_Const y a (fun n => rfl))
    have convy : IsConverges y := ⟨a, convya⟩
    have := Converges_Le y x convy convx ynlexn
    rw [← (Converges_sLim_iff y convy a).1 convya]
    exact this

theorem Converges_ge_const' (x : ℕ → ℝ) (a b: ℝ) (convx : ConvergesTo x a) :
  (∀ n, x n ≥ b) → a ≥ b := by
    intro xngeb
    let y : ℕ → ℝ := (fun _ => b)
    have ynlexn : ∀n, y n ≤ x n := by
      intro n
      exact xngeb n
    have convya : ConvergesTo y b := (Converges_Const y b (fun n => rfl))
    exact Converges_Le' y x b a convya convx ynlexn

/-
定理 1.8 (2) (b)
-/
theorem Squeeze_Theorem (x y z : ℕ → ℝ) (a : ℝ) (convxa : ConvergesTo x a) (convya : ConvergesTo y a):
  (∀ n, x n ≤ z n ∧ z n ≤ y n) → ConvergesTo z a := by
    intro bet ε εpos
    have s3 := convxa ε εpos
    let ⟨n₁,h1⟩ := s3
    have s4 := convya ε εpos
    let ⟨n₂,h2⟩ := s4
    let n₀ := max n₁ n₂
    have s5 : ∀n ≥ n₀, |x n - a| < ε := by
      intro n ngen₀
      have n₀gen₁ : n₀ ≥ n₁ := Nat.le_max_left n₁ n₂
      exact h1 n (ge_trans ngen₀ n₀gen₁)
    have s6 : ∀n ≥ n₀, |y n - a| < ε := by
      intro n ngen₀
      have n₀gen₂ : n₀ ≥ n₂ := Nat.le_max_right n₁ n₂
      exact h2 n (ge_trans ngen₀ n₀gen₂)
    have s7 : ∀n ≥ n₀, a - ε < x n ∧ x n ≤ z n ∧ z n ≤ y n ∧ y n < a + ε := by
      intro n ngen₀
      repeat (any_goals apply And.intro)
      . have := s5 n ngen₀
        rw [abs_lt,lt_tsub_iff_left] at this
        exact this.left
      . exact (bet n).left
      . exact (bet n).right
      . have := s6 n ngen₀
        rw [abs_lt,] at this
        apply lt_add_of_neg_add_lt_left
        rw [add_comm]
        exact this.right
    have s8 : ∀n ≥ n₀, |a - z n| < ε := by
      intro n ngen₀
      rw [abs_lt]
      have := s7 n ngen₀
      apply And.intro
      . have := lt_of_le_of_lt this.right.right.left this.right.right.right
        linarith
      . have := lt_of_lt_of_le this.left this.right.left
        linarith
    apply Exists.intro n₀
    intro n ngen₀
    rw [abs_sub_comm]
    exact s8 n ngen₀

end Section1_2
