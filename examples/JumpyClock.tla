---- MODULE JumpyClock ----
EXTENDS Naturals

VARIABLES hour, minute, second

Init ==
  /\ hour = 0
  /\ minute = 0
  /\ second = 0

TotalSeconds(h, m, s) ==
  s + (m*60) + (h*60)

IsInFuture(h, m, s) ==
  TotalSeconds(h, m, s) > TotalSeconds(hour, minute, second)

Tick ==
/\ \E next_hour \in 0..23 :
    \E next_minute \in 0..59:
      \E next_second \in 0..59:
        /\ IsInFuture(next_hour, next_minute, next_second)
        /\ hour' = next_hour
        /\ minute' = next_minute
        /\ second' = next_second

Next == /\ Tick

Spec == Init /\ [][Next]_<<hour, minute, second>>
====
