
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
