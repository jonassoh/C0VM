/**************************************************************************/
/*              COPYRIGHT Carnegie Mellon University 2024                 */
/* Do not post this file or any derivative on a public site or repository */
/**************************************************************************/
/* C0VM abnormal termination
 * 15-122 Principles of Imperative Computation
 * Rob Simmons
 */

void c0_user_error(char *err);        // for calls to error() in C0
void c0_assertion_failure(char *err); // for failed assertions in C0
void c0_memory_error(char *err);      // for memory-related errors
void c0_value_error(char *err);       // for c0_value-related errors
void c0_arith_error(char *err);       // for arithmetic-related errors
