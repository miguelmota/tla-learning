---- MODULE Clock ----
EXTENDS Naturals

VARIABLES hour, minute, second

Init ==
  /\ hour = 0
  /\ minute = 0
  /\ second = 0

Tick ==
  /\ hour' = IF second = 59 /\ minute = 59
             THEN IF hour = 23
                  THEN 0
                  ELSE hour + 1
            ELSE hour
  /\ minute' = IF second = 59
               THEN IF minute = 59
                    THEN 0
                    ELSE minute + 1
               ELSE minute
  /\ second' = IF second = 59
               THEN 0
               ELSE second + 1

Next == /\ Tick

Spec == Init /\ [][Next]_<<hour, minute, second>>
====
