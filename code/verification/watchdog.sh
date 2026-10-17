#!/bin/bash
# restart the (resumable) full run whenever it exits before all classes are done
cd .
while true; do
  n=$(cut -d' ' -f1 run_out.txt 2>/dev/null | sort -un | wc -l)
  if [ "$n" -ge 58161 ]; then echo "ALL DONE $(date)" >> watchdog.log; break; fi
  echo "start $(date) done=$n" >> watchdog.log
  OMP_NUM_THREADS=${NT:-12} ./netrun17.exe classes17.txt 0 58161 run_out.txt run >> run_stdout.log 2>> run_stderr.log
  echo "exit code $? $(date)" >> watchdog.log
  sleep 5
done
