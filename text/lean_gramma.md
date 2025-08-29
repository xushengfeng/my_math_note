---
"id": "8d3627c5",
"name": "lean 语法",
"base": []
---

# lean 语法

## 超简单的例子

```lean
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  apply Or.inr
  assumption
  apply Or.inl
  assumption
```

你先不用理解他说了什么，我们只看结构。

第一行，`example`表示我要提出一个命题，后面有一大堆括号，每个括号都是题设，也就是有对象和前提。就像题目中“有命题 p 和 q”。然后有个`:`后面跟的是结论“`p ∨ q → q ∨ p`”。这就是一个命题，或者我们可以视为一道题目。最后的`:= by`可以对应我们写下的“证明：”这几个字。

下面几行，开头要加上空格，这里是两格，开头空格的数量一定要相同，这样美观且方便 lean 识别。我们再以这片区域的第一行举例子。

`  intro h`，开头的`have`，说的是要用一个叫 have 的策略（Tactic），简单地理解，就是说明了一个动作，跟在策略后面的就是策略作用的对象，好像“吃 我 饭”就是执行吃这个操作，“我”和“饭”就是对象。一般每行开头都是策略，然后后面跟着策略要指挥哪些东西，这些东西用空格隔开。

对于部分证明，你只需要懂得上面的语法就可以了。

再举个例子：

```lean
example (x : U) (A B C : Set U) (h1 : A ⊆ B) (h2 : B ⊆ C) (h3 : x ∈ A) : x ∈ C := by
  have h4 : x∈ B := h1 h3
  exact h2 h4
```

这个前提就有很多了，“已知 x，集合 ABC，已知条件 h1:A ⊆ B，条件 h2:B ⊆ C，条件 h3:x ∈ A. 求证 x ∈ C”就是这个题目的翻译。这里`have`策略的语法看起来有点特殊，我们到时候专门介绍，现在可以先不管。

> note
>
> 关于空格
>
> 有些空格是为了美观，去掉后不影响理解
> `example(x:U)(A B C:Set U)(h1:A⊆B)(h2:B⊆C)(h3:x∈A):x∈C:=by`这样写也没关系
> 但有些空格去掉后就乱了：`exacth2h4`x
> 有些地方不能插入空格：`exam ple`x
> 可以加空格的地方，你要加多少个都可以：`exact           h2    h4`
> 策略前面的空格一定要与，在视觉上与题目隔开来。只要保证每块前面的空格统一就可以了，比如你可以只用一个空格，一般为 2 个或 4 个，你用 tab 代替也可以。换行的时候编辑器会自动帮你加。

我们证明时，其实是在对前提和结论变形，最后匹配好，完成证明。每一步，每个策略，都是变形的过程。编辑器会提示当前行，有哪些前提，哪个目标（用`⊢`提示）。

## 进阶一点

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  exact hp
  apply And.intro
  exact hq
  exact hp
```

`exapmle`不用起名，`theorem`要给命题起个名字，这里是`test`。有了名字，你可以在其他命题的证明中使用，而`exapmle`证过的东西不能直接用，所以你明白为什么一个叫“例子”（example）一个叫“定理”（theorem）了吧，有没有名字，能不能引用的区别。

像上面的例子，其实是在进行分类讨论，把一个目标拆解开来，逐一证明。你可以不用理解具体的数学规则，体会一下分类，下面我添加了*注释*

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro -- 分情况（case），其中情况左（case left）的目标为p，情况右（case right）的目标为q ∧ p
  exact hp -- 证明了情况左，结束，跳到情况右
  apply And.intro -- 现在要证明情况右，我们把情况右又分成了两种情况（左1 q，右1 p）
  exact hq -- 证明了左1
  exact hp -- 证明了右1
```

你不用管情况叫什么，`And.intro`规定了两个情况分别叫`left`和`right`，但描述时容易搞混，所以这里我改了一下。上面的分类还是有点不清楚，我们可以加入空格分块，用或`·`给每块的*第一行*打上

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  · exact hp
  · apply And.intro
    · exact hq
    · exact hp
```

你甚至可以用`case xxx => `来分块：

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case left => exact hp
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp
```

一般情况下先证明左边再证明右边，但我们如果用`case`指定了左右，可以自由调换顺序证明：

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case right => -- 明确了左右，先证明右边也可以
    apply And.intro
    case left => exact hq
    case right => exact hp
  case left => exact hp
```
