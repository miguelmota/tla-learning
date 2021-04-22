---- MODULE ClockTick ----
VARIABLE clock

Init == clock \in {0,1}

Tick == IF clock = 0 THEN clock' = 1 ELSE clock' = 0

Spec == Init /\ [][Tick]_<<clock>> /\ WF_<<clock>>(Tick)
====
