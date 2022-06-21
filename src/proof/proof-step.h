#ifndef __PROOF_STEP_H
#define __PROOF_STEP_H

#include "proof/proof-id.h"
#include "proof/proof-type.h"
#include "symbolic/DAG.h"
#include "symbolic/context-handling.h"
#include "symbolic/veriT-DAG.h"
#include "utils/stack.h"

/*
  --------------------------------------------------------------
  Main data structure
  --------------------------------------------------------------
*/

typedef struct TSproof_step *Tproof_step;

TSstack(_proof_step, Tproof_step); /* typedefs Tstack_proof_step */

/**
   \author Pascal Fontaine, Haniel Barbosa
   \brief Deduction unit datastructure. */
struct TSproof_step
{
  Tproof_type type; /**< proof type */
  Tstack_DAG DAGs;  /**< DAGs the proof step */
  /* TODO: get rid of this */
  unsigned misc;                    /**< Used to eliminate unused parts in the
                                                     derivation */
  Tstack_unsigned reasons;          /**< proof ids of premisses */
  Tstack_DAG args;                  /**< arguments of proof step */
  Tstack_proof_step subproof_steps; /**< steps of subproof */
};

/*
  --------------------------------------------------------------
  Interface
  --------------------------------------------------------------
*/

/**
   \author Pascal Fontaine, Haniel Barbosa
   \brief creates a proof step
   \return a pointer to the proof step */
extern Tproof_step proof_step_new(void);

/**
   \author Pascal Fontaine, Haniel Barbosa
   \brief free proof step
   \param Pproof_step a pointer to the proof step to free */
extern void proof_step_free(Tproof_step *Pproof_step);

/**
   \author Pascal Fontaine, Haniel Barbosa
   \brief add DAG to proof step
   \param proof_step the proof step
   \param DAG the DAG to add */
extern void proof_step_add_DAG(Tproof_step proof_step, TDAG DAG);

/**
   \author Pascal Fontaine, Haniel Barbosa
   \brief add DAG as argument of proof step
   \param proof_step the proof step
   \param DAG the DAG argument to add
   \remark only for proof steps that are not of the subproof category */
extern void proof_step_add_arg(Tproof_step proof_step, TDAG DAG);

/**
   \author Pascal Fontaine, Haniel Barbosa
   \brief add proof_id of a premisse for proof step
   \param proof_step the proof step
   \param proof_id the premisse of the proof step
   \remark only for proof steps that are not of the subproof category */
extern void proof_step_add_reason(Tproof_step proof_step, Tproof proof_id);

/**
   \author Pascal Fontaine, Haniel Barbosa
   \brief add parameter to justify proof step
   \param proof_step the proof step
   \param param the parameter of the proof step
   \remark parameter is the position of the used literal??? */
extern void proof_step_add_param(Tproof_step proof_step, unsigned param);

#endif
