#ifndef RESPONSE_H
#define RESPONSE_H

/**
   \file response.h
   \author Pascal Fontaine

   \brief Function implementing the output of veriT
*/

#include <stdarg.h>
#include <stdio.h>

/*
  --------------------------------------------------------------
  response helpers
  --------------------------------------------------------------
*/

/**
   \author Pascal Fontaine
   \brief outputs anything on the output chosen by veriT_set_out_file
   \param format printf-like format
*/
void veriT_out(char *format, ...);

/**
   \author Pascal Fontaine
   \brief outputs anything on the output chosen by veriT_set_out_file
   \param format printf-like format
*/
void veriT_out_no_newline(char *format, ...);

/**
   \author Pascal Fontaine
   \brief outputs anything on the output chosen by veriT_set_err_file
   \param format printf-like format
*/
void veriT_err(char *format, ...);

/**
   \author Pascal Fontaine
   \brief outputs anything on the output chosen by veriT_set_err_file and exit
   \param format printf-like format
*/
void veriT_error(char *format, ...);

/**
   \author Pascal Fontaine
   \brief set a file for the error flow
   \param str path to the file
*/
void veriT_set_err_file(char *str);

/**
   \author Pascal Fontaine
   \brief set a file for the error flow
   \param str path to the file
*/
void veriT_set_out_file(char *str);

/**
   \author Pascal Fontaine
   \brief module initialisation
*/
void response_init(void);

/**
   \author Pascal Fontaine
   \brief module disposal
*/
void response_done(void);

/**
   \author David Deharbe
   \brief output communication channel for normal output
*/
extern FILE *veriT_out_file;

/**
   \author David Deharbe
   \brief output communication channel for diagnostic output
*/
extern FILE *veriT_err_file;

#endif
