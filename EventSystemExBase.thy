theory EventSystemExBase
  imports TimeTable Watchdog EventSystem
begin

subsection \<open>Events\<close>

datatype event =
  TICK                          \<comment> \<open>Overall tick operation\<close>
| DISPATCH nat                  \<comment> \<open>Dispatch to the scheduler for changing partition\<close>
| SWITCH ttbl_id switch_mode    \<comment> \<open>Switch timetable command\<close>
| PARTITION partition           \<comment> \<open>Signal change of partition\<close>
| WATCHDOG_ADD "task_id \<times> nat"  \<comment> \<open>Add task to watchdog chain\<close>
| WATCHDOG_TICK                 \<comment> \<open>Tick on watchdog chain\<close>
| WATCHDOG_REMOVE task_id       \<comment> \<open>Remove task from watchdog chain\<close>

end
