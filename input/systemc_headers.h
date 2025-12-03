#if !defined(STRATUS_HLS)
#define SC_INCLUDE_FX
#endif

#include <systemc.h>

#if defined(__CTOS__) || defined(CTOS_MODEL)
#include "ctos_fx.h"
using namespace ctos_sc_dt;
#endif

#if defined(MTI_SYSTEMC) || defined(VIVADO_HLS)
#define async_reset_signal_is reset_signal_is
#endif

#if defined(CATAPULT_SYSTEMC)
#include <ac_reset_signal_is.h>
#endif

#if defined(STRATUS_HLS)
#include <stratus_hls.h>
#include <cynw_fixed.h>
#include <esc.h>
#endif




