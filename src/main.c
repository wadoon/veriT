/**
   \mainpage veriT documentation

   \section intro_sec Introduction

   veriT is a Satisfiability Modulo Theory (SMT) solver.

   The solver is currently integrating a quantifier instantiation mechanism with
   decision procedures for the following: uninterpreted functions with equality,
   linear arithmetics on the real numbers, and semi-decision procedures for
   linear arithmetics on the integers. There is also experimental support
   for non-linear arithmetics on the real
   numbers (using third-party tool <a href="http://www.redlog.eu">Redlog</a>).

   \section execution_sec Execution

   The input of the solver is a proof obligation in one of the
   following formats:

   - SMT-LIB 2.0: This is the default input format and may be employed
   as long as interactive features and incrementality are not used.
   See http://www.smtlib.org for information on this format.

   - DIMACS: This format may be employed when one wants to use
   veriT as a SAT-solver (with proof production capabilities).

   SMT-LIB 1.2 is not supported.

   The solver may be executed in two modes: batch and interactive.

   In batch mode the solver expects as argument the name of a file name in one
   of the supported formats. In interactive mode the solver expects a series of
   supported SMT-LIB 2.0 commands. Several formulas may be added, and they are
   conjunctively checked for satisfiability. There is no provision for
   backtracking or incrementality.

   veriT may be used to produce proofs: when the result is unsat, a derivation
   of the result might be produced and checked by a third party. Proof
   production is only available in batch mode.

   Command-line options may be used to output information about the
   proof obligation or about the proof process itself into files or
   to the standard output stream. See the specific documentation
   modules for \ref arguments_user and \ref arguments_developer.

   \section smtlib_2_sec Support for SMT-LIB 2.0

   - Logics for which veriT is complete and proof-producing:
   - QF_LRA
   - QF_RDL
   - QF_UFLRA
   - QF_UF

   - Logics for which veriT is incomplete and proof-producing:
   - LRA
   - QF_IDL
   - QF_LIA
   - QF_LIRA
   - QF_UFIDL
   - QF_UFLIA
   - UFLRA
   - UFNIA

   - Logics for which veriT is incomplete:
   - AUFLIA
   - AUFLIRA
   - AUFNIRA
   - QF_AUFLIA
   - QF_AX
   - QF_NIA
   - QF_NRA
   - QF_UFNRA

   - veriT does not support logics with bit vectors (BV).

   The following commands are supported:
   - set-logic
   - set-info: :status and :version are supported.
   - get-info: :error-behavior, :name, :version, :authors, :status are
   supported.
   - set-option: :diagnostic-output-channel, :regular-output-channel,
   :print-success are supported.
   - get-option: only for the options listed with set-option
   - declare-sort
   - declare-fun
   - define-fun
   - assert
   - check-sat
   - echo
   - exit

   The following commands are parsed but are not supported:
   - push
   - pop
   - define-sort
   - get-assertions
   - get-unsat-core
   - get-value
   - get-assignment
   - get-proof

   veriT currently does not support indexed symbols as identifiers.

   \section install_sec Installation

   The source code is available on the Web at
   http://www.verit-solver.org/ , along with a series of binaries.

   To install the solver from the sources, once it is downloaded and unpacked,
   change to the top level directory and set the values in the file
   "Makefile.variables". Run the command line make.  This will automatically
   fetch some third-party components and compile the sources. To include support
   for non-linear arithmetics, the user needs to install Redlog (available at
   http://www.redlog.eu) in the directory extern/reduce. Once the build is
   complete, copy the binary program, named "veriT", to the location of your
   choice.

   \section licence_sec Licence

   veriT is distributed under the free BSD license. It uses LGPL library GMP,
   a parser generated by flex/bison, and, optionally, Redlog.

   \section authors_sec Authors

   Pascal Fontaine, David Deharbe are the two main developpers. Additional
   contributors include Diego Caminha, Thomas Bouton and Pablo Federico Dobal.

   The solver is being developed by the <a
   href="http://sites.google.com/site/forallufrn/people">ForAll</a>
   group at <a href="http://www.ufrn.br">Universidade Federal do Rio
   Grande do Norte</a> (Brazil) and the <a
   href="http://veridis.loria.fr">VeriDis</a> group at <a
   href="http://www.univ-lorraine.fr">Universit&eacute; de Lorraine</a> and
   <a href="http://www.loria.fr">LORIA</a> (France).

   \defgroup arguments_user Options

   \defgroup arguments_developer Developer options */

#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#ifdef DEBUG
#ifdef MACOS
#include <unistd.h>
#endif
#endif
#include "complete.h"
#include "parsers/dimacs/dimacs.h"
#include "parsers/smtlib2/smtlib2.h"
#include "pre/pre.h"
#include "proof/proof.h"
#include "symbolic/DAG-print.h"
#include "symbolic/DAG.h"
#include "utils/general.h"
#include "utils/options.h"
#include "utils/statistics.h"
#include "utils/sys.h"
#include "veriT-config.h"
#include "veriT.h"

#ifdef HAVE_WINDOWS_H
#include <windows.h>
#include "utils/veriT-signal.h"
#endif

/* TODO: make sure veriT_init contains EVERYTHING to initialise.
   Now, options and stats are outside */

/** \addtogroup arguments_user

    - --version

    veriT prints the current version identifier and exits. */
static bool option_version_and_exit = false;

/** \addtogroup arguments_user

    - --disable-banner

    The message identifying the program is not printed to stdout. */
static bool option_disable_banner;

/** \addtogroup arguments_developer

    - --print-proof-format-and-exit

    Loads formula, expands macros, applies selected simplifications,
    and prints on stdout in SMT format. */
/* TODO: update 2.0: Only for SMT-LIB 1.2. From 2.0 on, use commands. */
static bool option_proof_format_and_exit;

/** \addtogroup arguments_user

    - --input=(smtlib2|dimacs)

    Sets the input format (smtlib2 is default). */
static char *input_format = NULL;

/** \addtogroup arguments_user

    - --disable-print-success

    Overrides the default SMT-LIB 2 behavior regarding the option
    :print-success. */
static bool option_disable_print_success = false;

/**
   @}
*/

static char *filename = NULL;

/*
  --------------------------------------------------------------
  Some output
  --------------------------------------------------------------
*/

static void
output_version_and_exit(FILE *out)
{
  fprintf(out, "This is %s, version %s\n", PACKAGE_NAME, PACKAGE_VERSION);
  veriT_exit(0);
}

static void
output_banner(FILE *out)
{
  if (option_disable_banner == 0)
    fprintf(out,
            "%s (%s) - the SMT-solver veriT (UFRN/LORIA).\n",
            PACKAGE_NAME,
            PACKAGE_VERSION);
}

/*
  --------------------------------------------------------------
  Core function
  --------------------------------------------------------------
*/

static Tstack_Pchar filename_table = NULL;
static FILE *input_file = NULL;

static void
set_options(void)
{
  /* DD+PF setup, declare and parse options */
  options_setup(filename_table,
                "veriT",
                PACKAGE_STRING,
                PACKAGE_BUGREPORT,
                "FILENAME",
                "The veriT solver "
                "-- checking verification conditions with theories.",
                "",
                "VERIT_");
  options_new(0,
              "version",
              "Prints version identifier and exits",
              &option_version_and_exit);
  options_new_string('i',
                     "input",
                     "input format (smtlib2 is default)",
                     "(smtlib2|dimacs)",
                     &input_format);
  input_format = strmake("smtlib2");
  options_new_string('o',
                     "output",
                     "output format (smtlib2 is default)",
                     "(smtlib2|b|py_graph)",
                     &output_format);
  output_format = strmake("smtlib2");
  options_new(0,
              "proof-format-and-exit",
              "Print proof format on stdout and exits",
              &option_proof_format_and_exit);
  options_new(0,
              "parse-only",
              "Loads formula, simplifies,"
              "and exit (smt)",
              &option_parse_only);
  options_new(0,
              "print-simp-and-exit",
              "Loads formula, simplifies,"
              "and print on stdout (smt)",
              &option_print_simp_and_exit);
  options_new(0,
              "print-flat",
              "print formula in flattened mode"
              " (no shared subterms or formulas)",
              &DAG_fprint_opt.flat);
  options_new(0,
              "disable-banner",
              "Disable printing of program banner",
              &option_disable_banner);
  options_new('s',
              "disable-print-success",
              "Do not print 'success' after each SMT-LIB 2 command",
              &option_disable_print_success);
#if defined(HAVE_POSIX_TIMER) || defined(HAVE_WINDOWS_H)
  options_new_int(
      0,
      "max-time",
      "Wall clock time limit for solving, Overwrites max-virtual-time",
      "MILLISECONDS",
      &option_max_time);
#endif
#if defined(HAVE_POSIX_TIMER)
  options_new_int(0,
                  "max-virtual-time",
                  "CPU time limit for solving",
                  "MILLISECONDS",
                  &option_max_virtual_time);
#endif
}
#define STATS_LEVEL 1

#if defined(HAVE_WINDOWS_H)
VOID CALLBACK
windows_timeout(PVOID lpParam, BOOLEAN TimerOrWaitFired)
{
  fprintf(stderr, TIMEOUT_TEXT);
  /* Unfortunately we can't do a proper exit here, since Windows uses threads to
   * implement this. */
  exit(VERIT_SIGALRM);
}
#endif

int
main(int argc, char **argv)
{
#ifdef DEBUG
  setbuf(stdout, 0); /* makes it easier to catch bugs */
#endif

  veriT_init();
  DAG_smtlib_logic_init();

  stack_INIT(filename_table);

  set_options();
  options_parse(argc, argv);
  veriT_set();
  stats_monitor_init();

  if (option_version_and_exit)
    output_version_and_exit(stdout);

  /* output some basic information */
  output_banner(stdout);

  if (option_proof_format_and_exit)
    {
      proof_doc(stdout);
      proof_satisfiable();
      veriT_exit(0);
    }

#if defined(HAVE_POSIX_TIMER)
  if (option_max_time || option_max_virtual_time)
    {
      if (option_max_time < 0 || option_max_virtual_time < 0)
        {
          fprintf(stderr, "Negative time limit\n");
          options_usage(stderr);
          veriT_exit(-1);
        }

      int which = ITIMER_VIRTUAL;
      if (option_max_time)
        {
          option_max_virtual_time = option_max_time;
          which = ITIMER_REAL;
        }

      struct itimerval its;
      its.it_value.tv_sec = option_max_virtual_time / 1000;
      its.it_value.tv_usec = (option_max_virtual_time % 1000) * 1000;
      its.it_interval.tv_sec = 0;
      its.it_interval.tv_usec = 0;
      if (setitimer(which, &its, NULL) == -1)
        {
          fprintf(stderr, "Failed to set timer\n");
          veriT_exit(-1);
        }
    }
#else
#if defined(HAVE_WINDOWS_H) && !defined(HAVE_POSIX_TIMER)
  if (option_max_time)
    {
      windows_timer_queue = CreateTimerQueue();
      if (windows_timer_queue == NULL)
        {
          fprintf(stderr, "Failed to create timer queue\n");
          veriT_exit(-1);
        }
      HANDLE hTimer;
      if (!CreateTimerQueueTimer(&hTimer,
                                 windows_timer_queue,
                                 (WAITORTIMERCALLBACK)windows_timeout,
                                 NULL,
                                 option_max_time,
                                 0,
                                 0))
        {
          fprintf(stderr, "Failed to set timer\n");
          veriT_exit(-1);
        }
    }
#endif
#endif

  if (stack_size(filename_table) > 1)
    {
      fprintf(stderr, "Only one file name is allowed\n");
      options_usage(stderr);
      veriT_exit(-1);
    }

  if (stack_size(filename_table) == 1)
    {
      /* parse file */
      filename = stack_get(filename_table, 0);
      input_file = sys_open_file(filename, "r");
      proof_set_input_file(filename);
    }
  else
    input_file = stdin;
  if (option_proof_file_from_input || option_proof_filename || proof_stats)
    proof_on = true;
  if (!strcmp(input_format, "smtlib2"))
    parse_smtlib2(input_file, option_disable_print_success);
  else if (!strcmp(input_format, "dimacs"))
    parse_dimacs(input_file);

  if (input_file != stdin)
    sys_close_file(input_file);

  veriT_exit(0);
  return 0; /* no gcc warning */
}