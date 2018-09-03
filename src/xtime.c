/* Precise timing of a process */

#include <stdio.h>
#include <fcntl.h>
#include <errno.h>
#include <stdlib.h>
#include <sys/time.h>
#include <sys/times.h>
#include <sys/resource.h>
#include <unistd.h>
#include <string.h>
#include <sys/wait.h>

int main(argc, argv)
     int argc;
     char ** argv;
{
  int nruns, i;
  struct rusage rusage;
  double user, system, total;
  char * output, * error;
  char * endptr;
  int outfd, errfd;
  int status;
  clock_t st_time;
  clock_t en_time;
  struct tms st_cpu;
  struct tms en_cpu;

  int fd;
  nruns = 1;
  output = NULL;
  error = NULL;
  argv += 1;
  while(*argv != NULL && *argv[0] == '-') {
    if (strcmp(*argv, "-o") == 0 && argv[1] != NULL) {
      output = argv[1];
      argv += 2;
    } else
    if (strcmp(*argv, "-e") == 0 && argv[1] != NULL) {
      error = argv[1];
      argv += 2;
    } else
    if (strcmp(*argv, "-repeat") == 0 && argv[1] != NULL) {
      nruns = strtol(argv[1], &endptr, 0);
      if (*endptr != '\0' || *argv[1] == '\0' || nruns <= 0) {
	fprintf(stderr, "Incorrect argument to -repeat, defaults to 1\n");
	nruns = 1;
      }
      argv += 2;
    } else {
      fprintf(stderr, "Usage: xtimehard [-o stdout] [-e stderr] [-c1 evt] [-c0 evt] [-repeat count] cmd args\n");
      exit(2);
    }
  }
#ifdef __CYGWIN__
  st_time = times(&st_cpu);
#endif
  for (i = 0; i < nruns; i++) {

    switch(fork()) {
    case -1:
      perror("xtime: fork failed"); exit(2);
    case 0:
      if (output != NULL) {
        outfd = open(output, O_WRONLY | O_CREAT | O_TRUNC, 0666);
        if (outfd == -1) {
          perror(output);
          exit(2);
        }
        dup2(outfd, 1);
      }
      if (error != NULL) {
        errfd = open(error, O_WRONLY | O_CREAT | O_TRUNC, 0666);
        if (errfd == -1) {
          perror(error);
          exit(2);
        }
        dup2(errfd, 2);
      }
      execvp(*argv, argv);
      fprintf(stderr, "xtime: cannot execute %s\n", *argv);
      exit(2);
    default:
      if (wait(&status) == -1) {
        fprintf(stderr, "xtime: wait error %d\n", errno);
	exit(2);
      }
      if (status != 0){
	fprintf(stderr, "xtime: error in child process (status : %d)\n", status);
	exit(2);
      }
      break;
    } /* switch */

  } /* for i */

#ifdef __CYGWIN__
  en_time = times(&en_cpu);
  total = ((double)(en_time - st_time))/sysconf(_SC_CLK_TCK);
  printf("%.3fs (elapsed: user + system + other processes)\n", total);
#else
  getrusage(RUSAGE_CHILDREN, &rusage);
  user = (rusage.ru_utime.tv_sec + rusage.ru_utime.tv_usec * 1e-6) / nruns;
  system = (rusage.ru_stime.tv_sec + rusage.ru_stime.tv_usec * 1e-6) / nruns;
  printf("%.3fs (user %.3fs + system %.3fs), max rss %ldK\n",
         user + system, user, system,
         rusage.ru_maxrss);
#endif
  return 0;
}
