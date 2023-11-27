# Benchmarks

These benchmarks were taken from SMT-COMP'23. They were downloaded from
[StarExec][1], unzipped, and post-processed with
```
$ find bench/ -name "starexec_description.txt" -exec rm -v {} \;
```

Additionally, the `20210312-Bouvier/` and `bcnscheduling/` folders were removed
since they use non-standard expressions.

[1]: https://www.starexec.org/starexec/secure/explore/spaces.jsp?id=538454
