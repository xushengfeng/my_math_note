---
"id": "3e9d8980",
"name": "基本数学概念与 Lean 示例",
"base": []
---

# 基本数学概念与 Lean 示例

## 自然数

自然数是正整数（1, 2, 3, ...）或非负整数（0, 1, 2, 3, ...），取决于上下文。在 Lean 中，自然数可以直接用数字表示：

```lean
#check (0 : Nat) -- 0
```

## 小数、分数

小数是十进制表示法，分数是整数之比（a/b，b≠0）。Lean 中可用有理数类型`Rat`表示分数：

```lean
#check (1/2 : Rat)  -- 1/2
#check (0.5 : Float) -- 浮点数表示
```

## 负数

负数是小于零的数，在数轴上位于原点左侧。Lean 中整数类型`Int`包含负数：

```lean
#check (-3 : Int)   -- -3
```

## 等式、不等式

等式表示相等关系（a = b），不等式表示不等关系（a < b, a > b 等）。Lean 中使用标准关系符号：

```lean
example : 2 + 2 = 4 := rfl
example : 3 < 5 := by decide
```

## 四则运算

加、减、乘、除四种基本运算。Lean 支持这些运算：

```lean
example : 3 + 4 = 7 := rfl
example : 8 - 2 = 6 := rfl
example : 3 * 4 = 12 := rfl
example : 12 / 4 = 3 := rfl
```

## 有理数、无理数

有理数可表示为分数，无理数不能（如 √2, π）。Lean 中：

```lean
#check (2/3 : Rat)    -- 有理数
-- 无理数通常需要实数类型和更高级的库
```

[假装这里有个证明](q:0123adf?showAnswer)

## 一元一次方程

形如 ax + b = 0 的方程。Lean 中可以证明解的正确性：

```lean
variable (a b x : ℝ) (ha : a ≠ 0)
example (h : a * x + b = 0) : x = -b / a := by
  field_simp
  linarith
```

## 数幂

乘方运算，aⁿ 表示 a 自乘 n 次。Lean 中使用`^`符号：

```lean
example : 2^3 = 8 := rfl
example : 5^0 = 1 := rfl
```

## 绝对值

数在数轴上到原点的距离，非负。Lean 中：

```lean
#check abs (-5)    -- 5
example : abs (-3) = 3 := rfl
```

## 一次函数

形如 f(x) = kx + b 的函数。Lean 中可以定义和证明性质：

```lean
def linear_function (k b x : ℝ) := k * x + b

example (k b : ℝ) : linear_function k b 0 = b := by
  simp [linear_function]
```

## 分式方程

含有分式的方程。Lean 中需要处理分母不为零的条件：

```lean
variable (x : ℝ) (hx : x ≠ 1)
example : (2/(x-1)) = 3 → x = 5/3 := by
  intro h
  field_simp at h ⊢
  linarith
```

## 一元二次方程

形如 ax² + bx + c = 0 的方程。Lean 中可验证求根公式：

```lean
variable (a b c x : ℝ) (ha : a ≠ 0)
theorem quadratic_formula (h : a*x^2 + b*x + c = 0) :
  x = (-b + Real.sqrt (b^2 - 4*a*c))/(2*a) ∨
  x = (-b - Real.sqrt (b^2 - 4*a*c))/(2*a) := by
  -- 证明需要更多工作，这里展示定理陈述
  sorry
```

这些示例展示了如何在 Lean 中形式化中小学数学的基本概念，为更高级的数学形式化打下基础。
