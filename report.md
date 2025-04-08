Работу выполнили студенты
```
Ушаков Александр,
Добронравов Алексей,
Майстренко Дмитрий
группа 5130904/10103,
```

# Описание выбранной foundation model
foundation model - это базовая модель, используемая для инициализации большого количества задач. Она может быть использована для многих задач, таких как генерация текста, машинное обучение, компьютерное зрение, обработка естественного языка, а также для создания других моделей.

DeepSeek — это семейство языковых и кодовых моделей, созданное компанией DeepSeek AI. DeepSeek — это трансформерная модель, которая была обучена на больших объемах текстовых и кодовых данных и может генерировать текст и программный код, близкие к созданным человеком. DeepSeek может быть использована для генерации текста, программирования, машинного перевода, кода, а также для других задач, связанных с обработкой естественного языка и искусственным интеллектом.

### Архитектура трансформера
Состоит из слоев энкодера и декодера (в GPT используется только декодер).
Включает механизмы само-внимания (Self-Attention), позволяющие модели учитывать контекст всей строки при генерации ответа.

### Обучение
Модель обучена на огромных объемах текстовых данных, включая книги, статьи, веб-сайты и другие источники.
- Предварительное обучение (Pre-training): Модель учится предсказывать следующее слово в предложении.
- Дополнительная настройка (Fine-tuning): С использованием RLHF (обучение с подкреплением с участием человека) для улучшения качества ответов.

### Параметры
Точное количество параметров не раскрывается, но предполагается, что GPT-4 значительно больше GPT-3 (который имел 175 миллиардов параметров).
Большее количество параметров позволяет модели лучше понимать сложные запросы и контекст.

# Описание простой системы управления заказом пиццы
## Общее описание системы
Система управления заказом пиццы моделирует жизненный цикл заказа от момента его размещения до завершения. Система позволяет отслеживать переходы между ключевыми этапами обработки заказа.

## Основные компоненты системы
### Модуль заказа пиццы
- Прием нового заказа.
- Перевод заказа в начальное состояние "Placed".

### Модуль обработки заказа
- Переход заказа в состояние "Preparing" после размещения.
- Подготовка ингредиентов и начало приготовления пиццы.

### Модуль приготовления пиццы
- Состояние "Baking": пицца находится в процессе выпекания.
- После завершения выпекания заказ переходит к доставке.

### Модуль доставки:
- Переход в состояние "Delivering", когда курьер забирает пиццу.
- Оповещение клиента о выезде курьера.

### Завершение заказа:
- Переход заказа в состояние "Completed", когда пицца доставлена клиенту.
- Возможность сразу начать новый заказ из завершенного состояния.

## Основные состояния заказа
| Состояние  | Описание                                                |
|------------|---------------------------------------------------------|
| Created    | Заказ создан, ожидание начала подготовки.               |
| Preparing  | Подготовка ингредиентов, начало процесса приготовления. |
| Baking     | Пицца в печи, заказ готовится к доставке.               |
| Delivering | Курьер в пути, пицца доставляется клиенту.              |
| Completed  | Заказ завершен, пицца доставлена. Возможен новый заказ. |

## Переходы между состояниями
### Размещение заказа (PlaceOrder)
- Состояние переходит из "Completed" в "Placed".
- Поддерживает возможность оформить новый заказ после завершения предыдущего.

### Подготовка пиццы (PreparePizza)
- Переход из "Placed" в "Preparing".
- Начинается сбор ингредиентов и подготовка к выпеканию.

### Выпекание пиццы (BakePizza)
- Переход из "Preparing" в "Baking".
- Пицца готовится в печи.

### Доставка пиццы (DeliverPizza)
- Переход из "Baking" в "Delivering".
- Пицца передана курьеру для доставки.

### Завершение заказа (CompleteOrder)
- Переход из "Delivering" в "Completed".
- Система готова принять новый заказ.

## Контроль за корректностью переходов (инварианты)
### Инвариант допустимых состояний
```
Invariant1 == orderState \in OrderStates
```
- Гарантирует, что система всегда находится в одном из допустимых состояний.

### Инвариант исключения нелогичных переходов
```
Invariant2 == ~(orderState = "Completed" /\ orderState = "Preparing")
```
- Предотвращает ситуацию, когда система одновременно находится в состояниях "Completed" и "Preparing".

### Запросы к foundation model
После того как мы уверенно определились с темой - начинаем работу над качественными запросами к foundation model.
Для начала дадим ему описание ожидаемой системы:
```
Hey man! I would like to create a description of a pizza order tracking system. Could you use TLA+ to model it?
Pizza Order Tracker
Description: Model a simple pizza order system.
States: Order Placed, Preparing, Baking, Delivering, Completed.
Actions: Transition between states based on order progress.
Invariants: Cannot be Delivered before Baked.
```
Запросы будем формировать на английском языке поскольку этот язык является native для foundation model.
Получаем следующий ответ от DeepSeek:
```tla+
----------------------------- MODULE PizzaOrderTracker -----------------------------
EXTENDS Naturals, Sequences

VARIABLES orderState

(* Define the possible states of the order *)
States == {"Order Created", "Preparing", "Baking", "Delivering", "Completed"}

(* Define the initial state *)
Init == orderState = "Order Created"

(* Define the possible transitions *)
Next ==
    \/ /\ orderState = "Order Created"
       /\ orderState' = "Preparing"
    \/ /\ orderState = "Preparing"
       /\ orderState' = "Baking"
    \/ /\ orderState = "Baking"
       /\ orderState' = "Delivering"
    \/ /\ orderState = "Delivering"
       /\ orderState' = "Completed"

(* Define the invariant: Cannot be Delivered before Baked *)
Invariant == 
    orderState = "Delivering" => orderState \in {"Baking", "Delivering", "Completed"}

(* Define the temporal specification *)
Spec == Init /\ [][Next]_orderState /\ WF_orderState(Next)

=============================================================================
```
Запускаем и видим ошибку:
![alt text](res/model_failed.png)

Со второго раза DeepSeek исправил ошибку, введя новый переход:
```
\/ /\ orderState = "Completed"
   /\ orderState' = "Order Created"
```

```tla+
----------------------------- MODULE PizzaOrderTracker -----------------------------
EXTENDS Naturals, Sequences

VARIABLES orderState

(* Define the possible states of the order *)
States == {"Order Created", "Preparing", "Baking", "Delivering", "Completed"}

(* Define the initial state *)
Init == orderState = "Order Created"

(* Define the possible transitions *)
Next ==
    \/ /\ orderState = "Order Created"
       /\ orderState' = "Preparing"
    \/ /\ orderState = "Preparing"
       /\ orderState' = "Baking"
    \/ /\ orderState = "Baking"
       /\ orderState' = "Delivering"
    \/ /\ orderState = "Delivering"
       /\ orderState' = "Completed"

(* Define the invariant: Cannot be Delivered before Baked *)
Invariant == 
    orderState = "Delivering" => orderState \in {"Baking", "Delivering", "Completed"}

(* Define the temporal specification *)
Spec == Init /\ [][Next]_orderState /\ WF_orderState(Next)

=============================================================================
```
Полученный ответ выглядит довольно убедительно, необходимо проверить работоспособность кода.
Запустим симуляцию нашей системы в Intellij Idea с помощью расширения TLA+:
![alt text](res/model_succeeded.png)

Видим что моделирование прошло успешно, не возникло никаких ошибок по типу Deadlock или нарушения инвариантов.
### Заключение
Получается, что модель смогла сгенерировать правильное описание системы на языке TLA+ с первого раза. Результат был ожидаем, поскольку запрос был поставлен довольно четко, плюс к тому же задача является довольно простой.

# Описание сложной системы управления заказами пиццы

Теперь попросим DeepSeek дополнить код так, чтобы описывалась система, которая может обрабатывать одновременно ограниченное множество заказов.

### Запросы к foundation model
```
It needs to be supplemented so that several orders can be made simultaneously.
```

Ответ модели:

---

To extend the PizzaOrderTracker module to handle multiple orders simultaneously, we need to modify the model to track the state of each order individually. Here's the supplemented version:
```tla+
----------------------------- MODULE PizzaOrderTracker -----------------------------
EXTENDS Naturals, Sequences

CONSTANT MaxOrders  \* The maximum number of concurrent orders to track

VARIABLES orders, nextOrderId

(* Define the possible states of an order *)
States == {"Order Created", "Preparing", "Baking", "Delivering", "Completed"}

(* Define the initial state *)
Init == 
    /\ orders = [id \in {} |-> "Order Created"]  \* Empty initial orders
    /\ nextOrderId = 1

(* Define the possible transitions *)
CanAdvance(id) == 
    \/ /\ orders[id] = "Order Created"
       /\ orders' = [orders EXCEPT ![id] = "Preparing"]
    \/ /\ orders[id] = "Preparing"
       /\ orders' = [orders EXCEPT ![id] = "Baking"]
    \/ /\ orders[id] = "Baking"
       /\ orders' = [orders EXCEPT ![id] = "Delivering"]
    \/ /\ orders[id] = "Delivering"
       /\ orders' = [orders EXCEPT ![id] = "Completed"]

CanCreateNewOrder ==
    /\ Cardinality(DOMAIN orders) < MaxOrders
    /\ orders' = [orders EXCEPT ![nextOrderId] = "Order Created"]
    /\ nextOrderId' = nextOrderId + 1

CanResetCompletedOrder(id) ==
    /\ orders[id] = "Completed"
    /\ orders' = [orders EXCEPT ![id] = "Order Created"]

Next ==
    \/ \E id \in DOMAIN orders: CanAdvance(id)
    \/ CanCreateNewOrder
    \/ \E id \in DOMAIN orders: CanResetCompletedOrder(id)

(* Define the invariant: Cannot be Delivered before Baked *)
Invariant ==
    \A id \in DOMAIN orders:
        orders[id] = "Delivering" => orders[id] \in {"Baking", "Delivering", "Completed"}

(* Define the temporal specification *)
Spec == Init /\ [][Next]_<<orders, nextOrderId>> /\ WF_<<orders, nextOrderId>>(Next)

=============================================================================
```

Key changes made:
1. Replaced orderState with orders (a function mapping order IDs to their states)
2. Added nextOrderId to track the next available order ID
3. Added MaxOrders constant to limit concurrent orders
4. Modified transitions to work with specific order IDs
5. Added ability to create new orders (CanCreateNewOrder)
6. Modified the invariant to apply to all orders
7. Updated the spec to include both variables in the fairness condition

This version allows:
- Multiple orders to exist simultaneously, each with their own state
- New orders to be created as long as we haven't reached MaxOrders
- Each order to progress independently through the states
- Completed orders to be reset to "Order Created" state

You would need to define MaxOrders when instantiating the model (e.g., MaxOrders == 5).

---

Модель указала нам, что нужно инстанцировать MaxOrders, но не указала где именно. Просим уточнить:

```
How exactly to define MaxOrder? Where?
```

Получаем ответ:

---
In TLA+, you define MaxOrders as a constant that must be specified when you create a model (in the TLC model checker) or when you instantiate the module. There are two ways to define it:

\### Option 1: Define it inside the module (as a default value)
If you want to provide a default value, you can define it directly in the module like this:

```tla+
----------------------------- MODULE PizzaOrderTracker -----------------------------
EXTENDS Naturals, Sequences

CONSTANTS MaxOrders  \* The maximum number of concurrent orders to track

ASSUME MaxOrders \in Nat \ {0}  \* Ensure MaxOrders is a positive integer

VARIABLES orders, nextOrderId

(* Rest of the module remains the same *)
=============================================================================
```
- When using TLC, you must still assign a value to MaxOrders in the model configuration.
- When using this module in another spec, you can override it.

\### Option 2: Define it in a separate configuration file (TLC Model Checker)
If you're using the TLC model checker, you define MaxOrders in the model configuration file (.cfg):

1. Create a file PizzaOrderTracker.cfg with:
   
```tla+
   CONSTANTS
       MaxOrders = 5  \* Allow up to 5 concurrent orders
```   
2. When running TLC, it will use this value.

\### Option 3: Define it when instantiating the module (for composition)
If you're using this module inside another spec, you can define MaxOrders when instantiating it:

```tla+
----------------------------- MODULE HigherLevelSpec -----------------------------
EXTENDS PizzaOrderTracker

INSTANCE PizzaOrderTracker WITH MaxOrders <- 10  \* Override MaxOrders here

(* Rest of your higher-level spec *)
=============================================================================
```
- This is useful if you want different instances with different limits.

\### Best Practice
- If MaxOrders is model-specific, define it in the .cfg file.
- If it should have a default value, define it in the module with ASSUME to enforce constraints.
- If you're composing specs, override it in INSTANCE WITH.

Would you like help setting up the TLC model checker for this?
---

Выбираем вариант с конфигом. Пробуем запустить, и получаем ошибку: 

```
Unknown operator: `Cardinality'.
Parsing or semantic analysis failed.
```

Указываем DeepSeek это и просим поправить:

```
Hey man I configured and wrote exactly how you said but when I tried to run it, I got a error:

Unknown operator: `Cardinality'.

Parsing or semantic analysis failed.

How to fix it?
```

Получаем ответ:

---
Ah, good catch! The Cardinality operator is not built into basic TLA+. You need to extend the FiniteSets module to use it. Here's the fix:

\### Updated Module (Fixed Version)

```tla+
----------------------------- MODULE PizzaOrderTracker -----------------------------
EXTENDS Naturals, Sequences, FiniteSets  \* <-- Added FiniteSets here

CONSTANT MaxOrders  \* The maximum number of concurrent orders to track

VARIABLES orders, nextOrderId

(* Define the possible states of an order *)
States == {"Order Created", "Preparing", "Baking", "Delivering", "Completed"}

(* Define the initial state *)
Init == 
    /\ orders = [id \in {} |-> "Order Created"]  \* Empty initial orders
    /\ nextOrderId = 1

(* Define the possible transitions *)
CanAdvance(id) == 
    \/ /\ orders[id] = "Order Created"
       /\ orders' = [orders EXCEPT ![id] = "Preparing"]
    \/ /\ orders[id] = "Preparing"
       /\ orders' = [orders EXCEPT ![id] = "Baking"]
    \/ /\ orders[id] = "Baking"
       /\ orders' = [orders EXCEPT ![id] = "Delivering"]
    \/ /\ orders[id] = "Delivering"
       /\ orders' = [orders EXCEPT ![id] = "Completed"]

CanCreateNewOrder ==
    /\ Cardinality(DOMAIN orders) < MaxOrders  \* Now works due to FiniteSets
    /\ orders' = [orders EXCEPT ![nextOrderId] = "Order Created"]
    /\ nextOrderId' = nextOrderId + 1

CanResetCompletedOrder(id) ==
    /\ orders[id] = "Completed"
    /\ orders' = [orders EXCEPT ![id] = "Order Created"]

Next ==
    \/ \E id \in DOMAIN orders: CanAdvance(id)
    \/ CanCreateNewOrder
    \/ \E id \in DOMAIN orders: CanResetCompletedOrder(id)

(* Define the invariant: Cannot be Delivered before Baked *)
Invariant ==
    \A id \in DOMAIN orders:
        orders[id] = "Delivering" => orders[id] \in {"Baking", "Delivering", "Completed"}

(* Define the temporal specification *)
Spec == Init /\ [][Next]_<<orders, nextOrderId>> /\ WF_<<orders, nextOrderId>>(Next)
=============================================================================
```

\### Key Fix
1. Added FiniteSets to the EXTENDS clause (this provides Cardinality).
2. Now Cardinality(DOMAIN orders) will work correctly.

\### Alternative (Without FiniteSets)
If you don’t want to use FiniteSets, you can replace:
```tla+
Cardinality(DOMAIN orders) < MaxOrders
```
with:
```tla+
\A id \in 1..MaxOrders: id \notin DOMAIN orders  \* Only allow new orders if some slots are free
```
But the FiniteSets approach is cleaner.

\### Next Steps
1. Save the updated module.
2. Ensure your .cfg file defines MaxOrders (e.g., MaxOrders = 3).
3. Re-run TLC—it should work now!

Let me know if you hit any other issues! 🚀
---

Выбираем подход с подключением FiniteSets и снова пробуем запустить. После чего наша программа работает слишком долго и не прекращает, что похоже на бесконечный цикл. Просим DeepSeek поправить это:

```
Man I have written exactly code you provided (with FiniteSets) but now my program got to some kind of infitity loop...
```

Получаем ответ:

---
Ah, I see the issue! The current spec allows infinite order creation (since nextOrderId keeps increasing forever), which can cause TLC to run indefinitely. Let's fix this by bounding the order IDs and ensuring the system resets properly.

\### Revised Module (Fixes Infinite Behavior)
```tla+
----------------------------- MODULE PizzaOrderTracker -----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT MaxOrders  \* Maximum concurrent orders allowed

VARIABLES orders, nextOrderId

(* Possible states of an order *)
States == {"Order Created", "Preparing", "Baking", "Delivering", "Completed"}

(* Initial state: No orders, nextOrderId starts at 1 *)
Init == 
    /\ orders = [id \in {} |-> "Order Created"]
    /\ nextOrderId = 1

(* Helper: Check if we can create a new order *)
CanCreateNewOrder ==
    /\ Cardinality(DOMAIN orders) < MaxOrders
    /\ orders' = [orders EXCEPT ![nextOrderId] = "Order Created"]
    /\ nextOrderId' = nextOrderId + 1

(* Helper: Advance an order to the next state *)
CanAdvance(id) == 
    \/ /\ orders[id] = "Order Created"
       /\ orders' = [orders EXCEPT ![id] = "Preparing"]
    \/ /\ orders[id] = "Preparing"
       /\ orders' = [orders EXCEPT ![id] = "Baking"]
    \/ /\ orders[id] = "Baking"
       /\ orders' = [orders EXCEPT ![id] = "Delivering"]
    \/ /\ orders[id] = "Delivering"
       /\ orders' = [orders EXCEPT ![id] = "Completed"]

(* Helper: Reset a completed order (optional) *)
CanResetCompletedOrder(id) ==
    /\ orders[id] = "Completed"
    /\ orders' = [orders EXCEPT ![id] = "Order Created"]

(* Next-state relation: Only allow new orders if below MaxOrders *)
Next ==
    \/ \E id \in DOMAIN orders: CanAdvance(id)
    \/ CanCreateNewOrder
    \/ \E id \in DOMAIN orders: CanResetCompletedOrder(id)

(* Invariant: No order skips "Baking" before "Delivering" *)
Invariant ==
    \A id \in DOMAIN orders:
        orders[id] = "Delivering" => orders[id] \in {"Baking", "Delivering", "Completed"}

(* Temporal spec: Init + always Next + weak fairness *)
Spec == Init /\ [][Next]_<<orders, nextOrderId>> /\ WF_<<orders, nextOrderId>>(Next)

(* BOUNDARY CONDITION: Prevent nextOrderId from growing infinitely *)
OrderIdBoundary == nextOrderId \leq MaxOrders * 2  \* Adjust multiplier as needed
=============================================================================
```

\### Key Fixes
1. Bounded nextOrderId  
   - Added OrderIdBoundary to prevent nextOrderId from growing infinitely.  
   - You can adjust MaxOrders * 2 (or any reasonable limit) in the .cfg file.

2. Strict Order Creation  
   - CanCreateNewOrder now only fires if orders hasn't reached MaxOrders.

3. Optional: Reset Orders  
   - CanResetCompletedOrder is optional—remove it if you don’t want orders to reset.

\---

\### TLC Model Configuration (.cfg)
```tla+
CONSTANTS
    MaxOrders = 3  \* Test with a small number first

INVARIANTS
    Invariant
    OrderIdBoundary  \* Enforce the boundary condition
```

\### Why It Was Looping Before
- Without OrderIdBoundary, nextOrderId could grow indefinitely, causing TLC to explore an infinite state space.
- The CanCreateNewOrder action kept firing even when unnecessary.

\### Next Steps
1. Run TLC with a small MaxOrders (e.g., 2 or 3) to verify behavior.
2. Remove CanResetCompletedOrder if you don’t need it (simplifies the model).
3. Increase MaxOrders gradually once the small case works.

Let me know if you need further refinements! 🍕
---

Вносим соответствующие изменения, снова пробуем запустить. Получаем следующую ошибку: `Invariant OrderIdBoundary is violated`

Сообщаем об этом модели:

```
Man, now I have error: Invariant OrderIdBoundary is violated... Please write working code
```

Получаем ответ:

---
I understand the frustration! Let's simplify the model to ensure it works correctly without infinite behavior. Here's a fully working version that avoids the OrderIdBoundary issue by reusing completed order IDs instead of letting nextOrderId grow infinitely.

\### Final Working Code (No Infinite Loops, No Boundary Errors)
```tla+
----------------------------- MODULE PizzaOrderTracker -----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT MaxOrders  \* Maximum concurrent orders allowed

VARIABLES orders

(* Possible states of an order *)
States == {"Order Created", "Preparing", "Baking", "Delivering", "Completed"}

(* Initial state: No orders *)
Init == orders = [id \in {} |-> "Order Created"]

(* Helper: Get the next available order ID (reuse completed ones first) *)
AvailableOrderId ==
    LET completed_ids == {id \in DOMAIN orders: orders[id] = "Completed"}
    IN IF completed_ids /= {} THEN CHOOSE id \in completed_ids : TRUE
       ELSE IF Cardinality(DOMAIN orders) < MaxOrders THEN Cardinality(DOMAIN orders) + 1
       ELSE -1  \* No available ID (should not happen due to CanCreateNewOrder guard)

(* Helper: Create a new order if possible *)
CanCreateNewOrder ==
    /\ Cardinality(DOMAIN orders) < MaxOrders
    /\ LET new_id == AvailableOrderId
       IN orders' = [orders EXCEPT ![new_id] = "Order Created"]

(* Helper: Advance an order to the next state *)
CanAdvance(id) == 
    \/ /\ orders[id] = "Order Created"
       /\ orders' = [orders EXCEPT ![id] = "Preparing"]
    \/ /\ orders[id] = "Preparing"
       /\ orders' = [orders EXCEPT ![id] = "Baking"]
    \/ /\ orders[id] = "Baking"
       /\ orders' = [orders EXCEPT ![id] = "Delivering"]
    \/ /\ orders[id] = "Delivering"
       /\ orders' = [orders EXCEPT ![id] = "Completed"]

(* Next-state relation *)
Next ==
    \/ \E id \in DOMAIN orders: CanAdvance(id)
    \/ CanCreateNewOrder

(* Invariant: No order skips "Baking" before "Delivering" *)
Invariant ==
    \A id \in DOMAIN orders:
        orders[id] = "Delivering" => orders[id] \in {"Baking", "Delivering", "Completed"}

(* Temporal spec: Init + always Next + weak fairness *)
Spec == Init /\ [][Next]_orders /\ WF_orders(Next)
=============================================================================
```

\### Key Improvements
1. No more nextOrderId  
   - Instead of infinitely increasing IDs, we reuse completed order IDs (AvailableOrderId).
   - If no completed orders exist, we assign a new ID (up to MaxOrders).

2. Guaranteed termination  
   - Since we never exceed MaxOrders, TLC won't explore infinite states.

3. Simpler fairness condition  
   - Only orders is tracked in fairness (WF_orders(Next)).

\---

\### TLC Model Configuration (.cfg)
```tla+
CONSTANTS
    MaxOrders = 3  \* Test with a small number first

INVARIANTS
    Invariant
```

\### How It Works Now
- New orders are created only if Cardinality(DOMAIN orders) < MaxOrders.
- IDs are recycled from completed orders (no infinite growth).
- No boundary condition needed (simpler and more reliable).

\### Testing
1. Run TLC with MaxOrders = 2 or 3 to verify correctness.
2. Check the state space—it should now be finite and manageable.

This version should work without errors in TLC. Let me know if you need further adjustments! 🚀
---

Пробуем запустить и снова получаем ошибку:

```
Could not find declaration or definition of symbol '-.'.
Couldn't resolve prefix operator symbol `-.'.
Parsing or semantic analysis failed.
```

Снова сообщаем модели об ошибке:

```
Now the error is 

Could not find declaration or definition of symbol '-.'.

Couldn't resolve prefix operator symbol `-.'.

Parsing or semantic analysis failed.
```

Получаем от DeepSeek следующий ответ:

---
Ah, I see the issue! The error occurs because TLA+ doesn't recognize -1 as a valid value in this context. Let's fix this by removing the -1 case and restructuring the AvailableOrderId definition to be more TLA+-friendly.

\### Final Corrected Working Code

```tla+
----------------------------- MODULE PizzaOrderTracker -----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT MaxOrders  \* Maximum concurrent orders allowed

VARIABLES orders

(* Possible states of an order *)
States == {"Order Created", "Preparing", "Baking", "Delivering", "Completed"}

(* Initial state: No orders *)
Init == orders = [id \in {} |-> "Order Created"]

(* Helper: Get the next available order ID (reuse completed ones first) *)
AvailableOrderId ==
    LET completed_ids == {id \in DOMAIN orders: orders[id] = "Completed"}
    IN IF completed_ids /= {} 
       THEN CHOOSE id \in completed_ids : TRUE
       ELSE IF Cardinality(DOMAIN orders) < MaxOrders 
            THEN Cardinality(DOMAIN orders) + 1
            ELSE CHOOSE id \in {} : FALSE  \* This case should never be reached due to CanCreateNewOrder guard

(* Helper: Create a new order if possible *)
CanCreateNewOrder ==
    /\ Cardinality(DOMAIN orders) < MaxOrders
    /\ LET new_id == AvailableOrderId
       IN orders' = [orders EXCEPT ![new_id] = "Order Created"]

(* Helper: Advance an order to the next state *)
CanAdvance(id) == 
    \/ /\ orders[id] = "Order Created"
       /\ orders' = [orders EXCEPT ![id] = "Preparing"]
    \/ /\ orders[id] = "Preparing"
       /\ orders' = [orders EXCEPT ![id] = "Baking"]
    \/ /\ orders[id] = "Baking"
       /\ orders' = [orders EXCEPT ![id] = "Delivering"]
    \/ /\ orders[id] = "Delivering"
       /\ orders' = [orders EXCEPT ![id] = "Completed"]

(* Next-state relation *)
Next ==
    \/ \E id \in DOMAIN orders: CanAdvance(id)
    \/ CanCreateNewOrder

(* Invariant: No order skips "Baking" before "Delivering" *)
Invariant ==
    \A id \in DOMAIN orders:
        orders[id] = "Delivering" => orders[id] \in {"Baking", "Delivering", "Completed"}

(* Temporal spec: Init + always Next + weak fairness *)
Spec == Init /\ [][Next]_orders /\ WF_orders(Next)
=============================================================================
```

\### Key Fixes:
1. Removed the -1 case which was causing the syntax error
2. Used CHOOSE id \in {} : FALSE as a safe alternative for the unreachable case
3. Guaranteed correctness by ensuring CanCreateNewOrder only fires when Cardinality(DOMAIN orders) < MaxOrders

\### Why This Works:
- The AvailableOrderId now either:
  - Reuses a completed order ID, or
  - Creates a new ID if under MaxOrders, or
  - Returns an empty choice (which is safe because CanCreateNewOrder prevents this case)
- No more syntax errors from invalid values
- Still maintains all the desired functionality

\### TLC Model Configuration (.cfg):
```
CONSTANTS
    MaxOrders = 3  \* Test with a small number first

INVARIANTS
    Invariant
```

This version should now run without any parsing errors in TLC. The model is both correct and finite. Let me know if you need any clarification or run into other issues!
---

Пробуем запустить и наконец получаем успех:

![image](https://github.com/user-attachments/assets/0c001e15-e595-4e68-a67e-0a48559c2aa2)

![image](https://github.com/user-attachments/assets/b29b6ca4-b548-4dbc-ab0c-62482c2183eb)

### Заключение:

Более сложную версию модель смогла выдать только спустя 6 итераций-запросов. Примечательно, что модель не пыталась протолкнуть один и тот же подход всё время: в предпоследней итерации, DeepSeek изменил подход, что помогло по итогу прийти к правильному решению.
Итого, модель смогла достигнуть цели лишь с указанием ей на ошибки, которые выдавал TLA+, непосредственные подсказки не понадобились. Знания разработчиком TLA+ не требуется - требуется лишь реализация TLA+, которая может указывать на ошибки.
