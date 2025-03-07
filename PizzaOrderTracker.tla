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