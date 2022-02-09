## Verifying partition scheduling using event systems

The code is tested on Isabelle2021 with AutoCorres 1.8.

https://isabelle.in.tum.de/

https://ts.data61.csiro.au/projects/TS/autocorres.pml.html


* ```EventSpecWhile```: definition and Hoare logic for event monads.
* ```EventSystem```: definition and Hoare logic for event systems.
* ```Mapreduce```: mapreduce example.

* ```Cache```: cache coherence protocol example.

* Partition scheduling case study:

  + ```TimeTable```: basics properties of time tables.

  + ```Watchdog```: functional specification of watchdog.

  + ```EventSystemExBase```: basic declarations for the case study.

  + ```EventSystemWatchdog```: verification of watchdog module.

  + ```EventSystemScheduler```: verification of no-switch case.

  + ```EventSystemSwitchScheduler```: verification of scheduler in the switching case.

  + ```EventSystemSwitch```: verification of overall system in the switching case.
