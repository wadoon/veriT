#include "pre/qsimp-by-unification.h"

#include <stdio.h>

#include "instantiation/discrimination-tree.h"
#include "instantiation/free-vars.h"
#include "instantiation/syntactic-unify.h"
#include "pre/pre.h"
#include "pre/simplify.h"
#include "symbolic/DAG-print.h"
#include "symbolic/DAG-symb-DAG.h"
#include "symbolic/DAG-tmp.h"
#include "symbolic/polarities.h"
#include "symbolic/veriT-DAG.h"
#include "utils/statistics.h"

#define QSIMP_STATS 0

#if QSIMP_STATS
static unsigned stat_ex_literals;
#endif

/* Construct possibly solvable terms */
typedef struct Spot_solution
{
  TDAG partner;                      /*< Term we should unify */
  Tpol polarity;                     /*< Polarity of partner */
  TDAG new_top;                      /*< The term with lit replaced by top */
  TDAG new_bot;                      /*< The term with lit replaced by bot*/
  Tstack_disc_tree_node index_nodes; /*< Index nodes for partner */
  Tstack_DAG existential_vars;       /*< Existential vars of partner  */
} Tpot_solution;

static inline TDAG
build_quantfier(TDAG target)
{
  assert(target != DAG_NULL);
  if (ground(target))
    return target;

  Tstack_DAG fvars = get_fvars(target);
  Tstack_DAG args;
  stack_INIT_s(args, stack_size(fvars) + 1);
  for (unsigned i = 0; i < stack_size(fvars); ++i)
    stack_push(args, stack_get(fvars, i));
  stack_push(args, target);
  TDAG r = DAG_dup(DAG_new_stack(QUANTIFIER_FORALL, args));
  DAG_free(target);
  stack_free(args);
  return r;
}

/* This only exists because stack_free is a macro */
static void
free_meta(void *s)
{
  stack_free(s);
}

#if QSIMP_DEBUG
static inline void
print_pol(Tpol pol)
{
  if (pol == POL_POS)
    printf("+ ");
  else if (pol == POL_NEG)
    printf("- ");
  else
    printf("ERROR ");
}
#endif

static inline TDAG
append(TDAG src, Tstack_DAG addition, Tstack_DAG suppress)
{
#if QSIMP_STATS
  stats_unsigned("qsimp/generated_terms",
                 "Terms generated by qsimp.",
                 "%6d",
                 stack_size(addition));
#endif
  TDAG r = src;
  if (!stack_is_empty(addition))
    {
      Tstack_DAG args;
      stack_INIT_s(args, DAG_arity(src) + stack_size(addition));
      for (unsigned i = 0; i < DAG_arity(src); ++i)
        {
          TDAG t = DAG_arg(src, i);
          if (!suppress || !stack_DAG_contains(suppress, t))
            stack_push(args, t);
        }
      for (unsigned i = 0; i < stack_size(addition); ++i)
        {
          TDAG t = stack_get(addition, i);
          if (!suppress || !stack_DAG_contains(suppress, t))
            stack_push(args, t);
        }
      r = DAG_dup(DAG_new_stack(DAG_symb(src), args));
      stack_apply(addition, DAG_free);
      stack_free(args);
      DAG_free(src);
    }
  stack_free(addition);
  return r;
}

/* free the date inside a Tpot_solution */
static inline void
free_pot_solution(Tpot_solution s)
{
  if (s.new_top != DAG_NULL)
    DAG_free(s.new_top);
  if (s.new_bot != DAG_NULL)
    DAG_free(s.new_bot);

  stack_free(s.index_nodes);
  stack_free(s.existential_vars);
}

static inline bool
is_symmertric(TDAG t)
{
  Tsymb s = DAG_symb(t);
  if (s == PREDICATE_EQ || s == CONNECTOR_EQUIV)
    return true;

  if (DAG_arity(t) == 2)
    {
      if (s == CONNECTOR_AND || s == CONNECTOR_OR)
        return true;
    }

  return false;
}

static Tpot_solution
eliminate(Tdisc_tree *index, TDAG src, Tpol polarity)
{
  Tpot_solution result = (Tpot_solution){0};
  Tstack_DAG existential_vars = NULL;
  Tpol local_polarity = POL_POS;
  /* We try to remove the term */
  if (quantifier(DAG_symb(src)))
    {
      if (QUANTIFIED_STRONG(src, polarity))
        {
          stack_INIT_s(existential_vars, DAG_arity(src) - 1);
          for (unsigned i = 0; i < DAG_arity(src) - 1; ++i)
            stack_push(existential_vars, DAG_arg(src, i));
          stack_sort(existential_vars, DAG_cmp_q);
          src = DAG_arg_last(src);
        }
      else if (QUANTIFIED_WEAK(src, polarity))
        {
          /* Just ignore the quantifier, we can do this because variables are
             never shadowed. */
          src = DAG_arg_last(src);
        }
      while (DAG_symb(src) == CONNECTOR_NOT)
        {
          local_polarity = INV_POL(local_polarity);
          src = DAG_arg0(src);
        }
    }

  Tstack_disc_tree_node nodes =
      disc_tree_lookup_vars_nodes(index, src, existential_vars);

  /* TODO: optimization: prune nodes which do not contain a term of proper
           quant_polarity */
  if ((nodes && !stack_is_empty(nodes)))
    {
      /* new is NULL for now: we have to remove this literal one step up */
      result = (Tpot_solution){.partner = src,
                               .polarity = local_polarity,
                               .new_top = DAG_dup(DAG_TRUE),
                               .new_bot = DAG_dup(DAG_FALSE),
                               .index_nodes = nodes,
                               .existential_vars = existential_vars};
    }

  if (result.partner == DAG_NULL)
    {
      if (existential_vars)
        stack_free(existential_vars);
      if (nodes)
        stack_free(nodes);
    }
  return result;
}

/* Helpers */

static inline void
mark_used(TDAG base, TDAG check, bool *marks)
{
  if (ground(check))
    return;
  Tstack_DAG base_vars = get_fvars(base);
  Tstack_DAG check_vars = get_fvars(check);
  for (unsigned i = 0; i < stack_size(check_vars); ++i)
    {
      TDAG v = stack_get(check_vars, i);
      int idx = stack_DAG_find(base_vars, v);
      if (idx != -1)
        marks[idx] = true;
    }
}

/* return true if any element of marks is false */
static inline bool
not_and(const unsigned n, const bool marks[n])
{
  for (unsigned i = 0; i < n; ++i)
    {
      if (!marks[i])
        return true;
    }
  return false;
}

static Tpot_solution
process(Tdisc_tree *index,
        TDAG src,
        Tpol polarity,
        bool might_eliminate,
        bool simplify_eagerly,
        bool use_solitary_heuristic)
{
  /* Quantifier: always try to remove */
  if (quantifier(DAG_symb(src)))
    return eliminate(index, src, polarity);

  if (DAG_symb(src) == CONNECTOR_NOT)
    {
      Tpol p = POL_POS;
      while (DAG_symb(src) == CONNECTOR_NOT)
        {
          p = INV_POL(p);
          src = DAG_arg0(src);
        }
      /* TODO: in proof producing mode we are not allowed to skip the negations
       */
      if (p == POL_NEG)
        {
          Tpot_solution s = process(index,
                                    src,
                                    INV_POL(polarity),
                                    might_eliminate,
                                    simplify_eagerly,
                                    use_solitary_heuristic);
          if (s.new_top != DAG_NULL)
            {
              assert(s.new_bot != DAG_NULL);
              TDAG s_neg_top = DAG_dup(DAG_new_unary(CONNECTOR_NOT, s.new_top));
              TDAG s_neg_bot = DAG_dup(DAG_new_unary(CONNECTOR_NOT, s.new_bot));
              DAG_free(s.new_top);
              DAG_free(s.new_bot);
              s.new_top = s_neg_top;
              s.new_bot = s_neg_bot;
            }
          return s;
        }
      return process(index,
                     src,
                     polarity,
                     might_eliminate,
                     simplify_eagerly,
                     use_solitary_heuristic);
    }

  /* Lets try to eliminate everything eagerly, but we can't do much if we
     have a nested quantifier. */
  if (might_eliminate && !DAG_quant(src))
    {
      Tpot_solution solution = eliminate(index, src, polarity);
      if (solution.partner != DAG_NULL)
        return solution;
    }

  /* Handle implications */
  if (DAG_symb(src) == CONNECTOR_IMPLIES)
    {
      TDAG left = DAG_arg0(src);
      TDAG right = DAG_arg1(src);

      bool me = simplify_eagerly;
      if (use_solitary_heuristic)
        {
          if (me && !ground(left))
            {
              unsigned n_vars = stack_size(get_fvars(left));
              bool *left_marks;
              MY_MALLOC(left_marks, sizeof(bool) * n_vars);
              memset(left_marks, 0, sizeof(bool) * n_vars);
              mark_used(left, right, left_marks);
              me = not_and(n_vars, left_marks);
              free(left_marks);
            }
          else
            me = false;
        }

      Tpot_solution left_solution = (Tpot_solution){0};
      if (simplify_eagerly || use_solitary_heuristic || !ground(left) ||
          DAG_quant(left))
        left_solution = process(index,
                                left,
                                INV_POL(polarity),
                                me,
                                simplify_eagerly,
                                use_solitary_heuristic);
      /* We check for a partner to test if we found a solution */
      if (left_solution.partner != DAG_NULL)
        {
          assert(left_solution.new_top != DAG_NULL);
          assert(left_solution.new_bot != DAG_NULL);
          TDAG s_imp_top = DAG_dup(
              DAG_new_binary(CONNECTOR_IMPLIES, left_solution.new_top, right));
          TDAG s_imp_bot = DAG_dup(
              DAG_new_binary(CONNECTOR_IMPLIES, left_solution.new_bot, right));
          DAG_free(left_solution.new_top);
          DAG_free(left_solution.new_bot);
          left_solution.new_top = s_imp_top;
          left_solution.new_bot = s_imp_bot;
          return left_solution;
        }

      if (use_solitary_heuristic)
        {
          if (me && !ground(right))
            {
              unsigned n_vars = stack_size(get_fvars(right));
              bool *right_marks;
              MY_MALLOC(right_marks, sizeof(bool) * n_vars);
              memset(right_marks, 0, sizeof(bool) * n_vars);
              mark_used(right, left, right_marks);
              me = not_and(n_vars, right_marks);
              free(right_marks);
            }
          else
            me = false;
        }

      Tpot_solution right_solution = (Tpot_solution){0};
      if (simplify_eagerly || use_solitary_heuristic || !ground(right) ||
          DAG_quant(right))
        right_solution = process(index,
                                 right,
                                 polarity,
                                 me,
                                 simplify_eagerly,
                                 use_solitary_heuristic);
      if (right_solution.partner != DAG_NULL)
        {
          assert(right_solution.new_top != DAG_NULL);
          assert(right_solution.new_bot != DAG_NULL);
          TDAG s_imp_top = DAG_dup(
              DAG_new_binary(CONNECTOR_IMPLIES, left, right_solution.new_top));
          TDAG s_imp_bot = DAG_dup(
              DAG_new_binary(CONNECTOR_IMPLIES, left, right_solution.new_bot));
          DAG_free(right_solution.new_top);
          DAG_free(right_solution.new_bot);
          right_solution.new_top = s_imp_top;
          right_solution.new_bot = s_imp_bot;
        }
      return right_solution;
    }

  /* Handle clause case */
  if (DAG_symb(src) == CONNECTOR_OR || DAG_symb(src) == CONNECTOR_AND)
    {
      for (unsigned j = 0; j < DAG_arity(src); ++j)
        {
          TDAG literal = DAG_arg(src, j);

          bool me = simplify_eagerly;
          if (use_solitary_heuristic)
            {
              if (me && !ground(literal))
                {
                  unsigned n_vars = stack_size(get_fvars(literal));
                  bool *marks;
                  MY_MALLOC(marks, sizeof(bool) * n_vars);
                  memset(marks, 0, sizeof(bool) * n_vars);
                  for (unsigned i = 0; i < DAG_arity(src); ++i)
                    {
                      if (i != j)
                        mark_used(literal, DAG_arg(src, i), marks);
                    }
                  me = not_and(n_vars, marks);
                  free(marks);
                }
              else
                me = false;
            }

          Tpot_solution solution = (Tpot_solution){0};
          if (simplify_eagerly || use_solitary_heuristic || !ground(literal) ||
              DAG_quant(literal))
            solution = process(index,
                               literal,
                               polarity,
                               me,
                               simplify_eagerly,
                               use_solitary_heuristic);
          if (solution.partner != DAG_NULL)
            {
              assert(solution.new_top != DAG_NULL);
              assert(solution.new_bot != DAG_NULL);
              /* Build target term */
              Tstack_DAG new_args;
              stack_INIT_s(new_args, DAG_arity(src));
              for (unsigned j_new = 0; j_new < DAG_arity(src); ++j_new)
                {
                  if (j_new == j)
                    {
                      stack_push(new_args, solution.new_top);
                    }
                  else
                    stack_push(new_args, DAG_arg(src, j_new));
                }
              assert(stack_size(new_args) > 1);
              TDAG new_src = DAG_dup(DAG_new_stack(DAG_symb(src), new_args));
              stack_reset(new_args);
              DAG_free(solution.new_top);
              solution.new_top = new_src;

              for (unsigned j_new = 0; j_new < DAG_arity(src); ++j_new)
                {
                  if (j_new == j)
                    {
                      stack_push(new_args, solution.new_bot);
                    }
                  else
                    stack_push(new_args, DAG_arg(src, j_new));
                }
              assert(stack_size(new_args) > 1);
              new_src = DAG_dup(DAG_new_stack(DAG_symb(src), new_args));
              stack_free(new_args);
              DAG_free(solution.new_bot);
              solution.new_bot = new_src;
              return solution;
            }
        }
    }

  return (Tpot_solution){0};
}

static inline void
process_potential_solution(Tdisc_tree *index,
                           const TDAG clause,
                           const TDAG partner,
                           const Tstack_disc_tree_node nodes,
                           const Tpot_solution potential_solution,
                           Tstack_DAG *result,
                           Tstack_DAG *suppress)
{
  Tpol polarity = potential_solution.polarity;
  assert(nodes != NULL && !stack_is_empty(nodes));
  for (unsigned i_node = 0; i_node < stack_size(nodes); ++i_node)
    {
      Tdisc_tree_node node = stack_get(nodes, i_node);
      assert(node != 0);
      Tstack_DAG terms = disc_tree_node_DAGs(index, node);
      Tstack_pol term_polarities = disc_tree_node_meta(index, node);
      assert(stack_size(terms) == stack_size(term_polarities));
      for (unsigned i_term = 0; i_term < stack_size(terms); ++i_term)
        {
          TDAG term = stack_get(terms, i_term);

          DAG_tmp_reserve();
          TDAG new_subst = DAG_NULL;
          if (unify_syntactic_vars(
                  term, partner, potential_solution.existential_vars))
            {
              if (polarity == stack_get(term_polarities, i_term))
                new_subst = apply_substitution(potential_solution.new_top);
              else
                new_subst = apply_substitution(potential_solution.new_bot);
            }
          reset_substitution(partner, term);
          DAG_tmp_release();

          /* We quantify only now, because we need DAG_tmp_DAG for this */
          if (new_subst != DAG_NULL)
            {
              set_fvars(new_subst);
#if DEBUG
              if (potential_solution.existential_vars && get_fvars(new_subst))
                {
                  Tstack_DAG ex_vars = potential_solution.existential_vars;
                  for (unsigned i = 0; i < stack_size(ex_vars); ++i)
                    {
                      TDAG e = stack_get(ex_vars, i);
                      assert(!stack_DAG_contains(get_fvars(new_subst), e));
                    }
                }
#endif
              new_subst = build_quantfier(new_subst);
              if (*suppress)
                stack_push(*suppress, potential_solution.partner);
#if QSIMP_STATS
              if (potential_solution.existential_vars)
                stats_counter_inc(stat_ex_literals);
#endif
#if QSIMP_DEBUG
              printf("--- Derived: ---");
              printf("\nClause:   ");
              DAG_print(clause);
              printf("\nPartner:  ");
              print_pol(polarity);
              DAG_print(potential_solution.partner);
              if (potential_solution.existential_vars)
                {
                  printf("\nEx Vars:  ");
                  for (unsigned i = 0;
                       i < stack_size(potential_solution.existential_vars);
                       ++i)
                    {
                      DAG_print(
                          stack_get(potential_solution.existential_vars, i));
                      printf(" ");
                    }
                }
              printf("\nNew Term (top case): ");
              DAG_print(potential_solution.new_top);
              printf("\nWith:     ");
              print_pol(stack_get(term_polarities, i_term));
              DAG_print(term);
              printf("\nResult:   ");
              DAG_print(new_subst);
              printf("\n");
#endif
              stack_push(*result, new_subst);
              new_subst = DAG_NULL;
            }
        }
    }
}

TDAG
qsimp_by_unification(TDAG src,
                     bool delete_simplified,
                     bool simplify_eagerly,
                     bool use_solitary_heuristic)
{
  /* Check if we have multiple clauses */
  if (!(DAG_symb(src) == CONNECTOR_AND))
    return src;

#if QSIMP_STATS
  unsigned stat_timer =
      stats_timer_new("qsimp/time", "time", "%7.2f", STATS_TIMER_ALL);
  stats_timer_start(stat_timer);
  unsigned stat_queue =
      stats_counter_new("qsimp/queue",
                        "Initial number of	elements in the qsimp queue.",
                        "%6d");
  stat_ex_literals = stats_counter_new(
      "qsimp/ex_literals", "Existential literals used by qsimp.", "%6d");
#endif

  Tdisc_tree *index = disc_tree_INIT();

  /* Build index using discrimination tree */
  for (unsigned i = 0; i < DAG_arity(src); i++)
    {
      /* Not necessary a clause, but for clarity we use that here */
      TDAG clause = DAG_arg(src, i);
      TDAG atom = DAG_NULL;
      Tpol polarity = POL_POS;

      if (DAG_symb(clause) == QUANTIFIER_FORALL)
        {
          assert(!get_fvars(clause) || stack_is_empty(get_fvars(clause)));

          TDAG inner = DAG_arg_last(clause);
          polarity = DAG_polarity(inner);
          atom = DAG_atom(inner);
        }
      else if (!quantifier(DAG_symb(clause)) && !DAG_quant(clause))
        {
          /* Insert ground terms without nested quantifier */
          /* Note: since there is normalization happening in this case, this
             likely only helps in a limited number of cases */
          assert(!get_fvars(clause) || stack_is_empty(get_fvars(clause)));

          polarity = DAG_polarity(clause);
          atom = DAG_atom(clause);
        }

      if (atom != DAG_NULL)
        {
          Tdisc_tree_node node = disc_tree_insert(index, atom);
          Tstack_pol polarities = disc_tree_node_meta(index, node);
          if (!polarities)
            {
              Tstack_pol new_polarities;
              stack_INIT(new_polarities);
              stack_push(new_polarities, polarity);
              disc_tree_node_set_meta(index, node, new_polarities);
            }
          else
            {
              stack_push(polarities, polarity);
              disc_tree_node_set_meta(index, node, polarities);
            }
        }
    }
#if QSIMP_STATS
  stats_unsigned("qsimp/indexed_terms",
                 "Terms within the index for qsimp.",
                 "%6d",
                 disc_tree_num_terms(index));
#endif

  Tstack_DAG queue;
  stack_INIT_s(queue, DAG_arity(src));
  for (unsigned i = 0; i < DAG_arity(src); i++)
    {
      /* Not necessary a clause, but for clarity we use that here */
      TDAG clause = DAG_arg(src, i);
      /* (not (exists... has been normalized at this point */
      if (DAG_symb(clause) == QUANTIFIER_FORALL)
        {
          if (simplify_eagerly || use_solitary_heuristic ||
              DAG_quant(DAG_arg_last(clause)))
            {
              assert(!get_fvars(clause) || stack_is_empty(get_fvars(clause)));
              stack_push(queue, clause);
            }
        }
    }

  Tstack_DAG result;
  stack_INIT(result);

  Tstack_DAG local_result;
  stack_INIT(local_result);

  /* Stack of DAGs that were simplified and hence should be thrown away.
   * This is no longer complete, but maybe speeds things up? */
  Tstack_DAG suppress = NULL;
  if (delete_simplified)
    stack_INIT(suppress);

  /* Now we have all the top level term, search for terms we can handle */
  while (!stack_is_empty(queue))
    {
#if QSIMP_STATS
      stats_counter_inc(stat_queue);
#endif
      /* Not necessary a clause, but for clarity we use that here */
      TDAG clause = stack_pop(queue);
      assert(DAG_symb(clause) == QUANTIFIER_FORALL);
      TDAG inner = DAG_arg_last(clause);
      Tpot_solution potential_solution = process(index,
                                                 inner,
                                                 POL_POS,
                                                 true,
                                                 simplify_eagerly,
                                                 use_solitary_heuristic);

      if (potential_solution.partner != DAG_NULL)
        {
          process_potential_solution(index,
                                     clause,
                                     potential_solution.partner,
                                     potential_solution.index_nodes,
                                     potential_solution,
                                     &local_result,
                                     &suppress);
        }

      free_pot_solution(potential_solution);
      if (delete_simplified && !stack_is_empty(local_result))
        stack_push(suppress, clause);
      while (!stack_is_empty(local_result))
        {
          TDAG t = stack_pop(local_result);
          t = pre_quant_ite(t);
          t = simplify_formula(t);
          set_fvars(t);
          if (DAG_symb(t) == QUANTIFIER_FORALL && DAG_quant(DAG_arg_last(t)))
            stack_push(queue, t);
          stack_push(result, t);
        }
    }
  stack_free(queue);
  stack_free(local_result);

  if (delete_simplified)
    stack_sort(suppress, DAG_cmp_q);
  disc_tree_meta_apply(index, free_meta);
  disc_tree_free(index);
  src = append(src, result, suppress);
  if (delete_simplified)
    stack_free(suppress);

#if QSIMP_STATS
  stats_timer_stop(stat_timer);
#endif
  return src;
}
