---------------------- MODULE AdvancedPizzaOrderTracker ----------------------
EXTENDS Naturals, Sequences

(* Определение состояний заказа *)
CONSTANTS MaxOrdersPrepared, OrdersPrior

VARIABLES orders, preparedOrders, inDelivery, waitingOrders, event, delayDelivery, delayIngredients

(* Перечисление состояний заказов *)
State == {"canceled", "prepared", "delivering", "pending"}

(* Определение переходов между состояниями для стандартных заказов *)
ExpressOrderProcess ==
    \E order \in waitingOrders :
        /\ orders[order] = "pending"
        /\ event = "delayed" => orders[order] = "prepared"
        /\ event = "none" => orders[order] = "pending"

(* Задержки, которые могут повлиять на состояние заказов *)
DelayConditions ==
    delayDelivery = "yes" \/ delayIngredients = "yes"

(* Проверка ограничений на количество подготовленных заказов *)
CheckMaxOrders ==
    \A i \in 1..MaxOrdersPrepared :
        orders[i] # "prepared" => orders[i] = "canceled"

 (* Определение переходов между состояниями для стандартных заказов *)
\*StandardOrderProcess ==
\*    \E order \in waitingOrders :
\*        /\ orders[order] = "pending"
\*\*        /\ \A i \in waitingOrders : orders[i] = "pending" => orders[order] = "prepared"
\*\*        /\ delayDelivery = "yes"
\*\*        /\ orders[order] = "delivering"

(* Инициализация системы *)
Init ==
    /\ orders = [i \in 1..MaxOrdersPrepared |-> "canceled"]
    /\ preparedOrders = [i \in 1..MaxOrdersPrepared |-> "canceled"]
    /\ inDelivery = [i \in 1..MaxOrdersPrepared |-> "canceled"]
    /\ waitingOrders = << >>
    /\ event = "none"
    /\ delayDelivery = "no"
    /\ delayIngredients = "no"

(* Основная система с процессами для стандартных и экспресс-заказов *)
Next ==
\*    \/ StandardOrderProcess
    \/ ExpressOrderProcess
    \/ CheckMaxOrders
    \/ DelayConditions

(* Запуск модели *)
Spec == Init /\ [Next]_<<orders, preparedOrders, inDelivery, waitingOrders, event, delayDelivery, delayIngredients>>

======================
