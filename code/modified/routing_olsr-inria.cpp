// Portions of this file
// Copyright (c) 2001-2009, Scalable Network Technologies, Inc.  All Rights Reserved.
//                          6100 Center Drive
//                          Suite 1250
//                          Los Angeles, CA 90045
//                          sales@scalable-networks.com
//
// This source code is licensed, not sold, and is subject to a written
// license agreement.  Among other things, no portion of this source
// code may be copied, transmitted, disclosed, displayed, distributed,
// translated, used as the basis for a derivative work, or used, in
// whole or in part, for any program or purpose other than its intended
// use in compliance with the license agreement as part of the QualNet
// software.  This source code and certain of the algorithms contained
// within it are confidential trade secrets of Scalable Network
// Technologies, Inc. and may not be used as the basis for any other
// software, hardware, product or service.

/*
 * This Copyright notice is in French. An English summary is given
 * but the referee text is the French one.
 *
 * Copyright (c) 2000, 2001 Adokoe.Plakoo@inria.fr, INRIA Rocquencourt,
 *                          Anis.Laouiti@inria.fr, INRIA Rocquencourt.
 *
 * Ce logiciel informatique est disponible aux conditions
 * usuelles dans la recherche, c'est-?dire qu'il peut
 * être utilis? copi? modifi? distribu??l'unique
 * condition que ce texte soit conserv?afin que
 * l'origine de ce logiciel soit reconnue.
 * Le nom de l'Institut National de Recherche en Informatique
 * et en Automatique (INRIA), ou d'une personne morale
 * ou physique ayant particip??l'élaboration de ce logiciel ne peut
 * être utilis?sans son accord préalable explicite.
 *
 * Ce logiciel est fourni tel quel sans aucune garantie,
 * support ou responsabilit?d'aucune sorte.
 * Certaines parties de ce logiciel sont dérivées de sources developpees par
 * University of California, Berkeley et ses contributeurs couvertes
 * par des copyrights.
 * This software is available with usual "research" terms
 * with the aim of retain credits of the software.
 * Permission to use, copy, modify and distribute this software for any
 * purpose and without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies,
 * and the name of INRIA, or any contributor not be used in advertising
 * or publicity pertaining to this material without the prior explicit
 * permission. The software is provided "as is" without any
 * warranties, support or liabilities of any kind.
 * This product includes software developed by the University of
 * California, Berkeley and its contributors protected by copyrights.
 */
// /**
// PROTOCOL :: OLSR-INRIA

// SUMMARY ::
// The Optimized Link State Routing Protocol (OLSR) is a kind of
// optimization of the pure link state protocol tuned to the
// requirements for mobile ad-hoc network. It operates as a table
// driven and proactive manner and thus exchanges topology information
// with other nodes of the network on periodic basis. Its main objective
// is to minimize the control traffic by selecting a small number of nodes,
// called multi-point relay (MPR) for flooding topological information. In
// route calculation, these MPR nodes are used to form an optimal route from
// a given node to any destination in the network. This routing protocol is
// particularly suited for a large and dense network.

// LAYER ::  Application Layer

// STATISTICS ::
// + numHelloReceived : number of hello received
// + numHelloSent     : number of hello sent
// + numTcReceived    : number of TC received
// + numTcGenerated   : number of TC generated
// + numTcRelayed     : number of TC relayed
// + numMidReceived   : number of MID received
// + numMidGenerated  : number of MID generated
// + numMidRelayed    : number of MID relayed
// + numHnaReceived   : number of HNA received
// + numHnaGenerated  : number of HNA generated
// + numHnaRelayed    : number of HNA relayed

// APP_PARAM ::

// CONFIG_PARAM ::
// + ROUTING-PROTOCOL         : OLSR-INRIA : Specification of OLSR-INRIA
//                                           as routing protocol
// + OLSR-IP-VERSION          : <IPv6|IPv4>
// + OLSR-HELLO-INTERVAL      : <time-interval>
// + OLSR-TC-INTERVAL         : <time-interval>
// + OLSR-MID-INTERVAL        : <time-interval>
// + OLSR-HNA-INTERVAL        : <time-interval>
// + OLSR-NEIGHBOR-HOLD-TIME  : <time-interval>
// + OLSR-TOPOLOGY-HOLD-TIME  : <time-interval>
// + OLSR-DUPLICATE-HOLD-TIME : <time-interval>
// + OLSR-MID-HOLD-TIME       : <time-interval>
// + OLSR-HNA-HOLD-TIME       : <time-interval>

// VALIDATION ::$QUALNET_HOME/verification/olsr-inria

// IMPLEMENTED_FEATURES ::
// + OLSR control messages and information repositories, that are required for route table computation.
// + Multiple OLSR-interfaces.
// + Support for IPv6 interoperability.
// + Injection of non OLSR-MANET route into OLSR-MANET domain.
// + OLSR control messages and Table entry timeout intervals are user configurable.
// + Forwarding OLSR unsupported control messages.
// + Operability with IPv4-IPv6 networks (DualIP support).


// OMITTED_FEATURES :: (Title) : (Description) (list)
// + A node does not support both IPv4 and IPv6 configurations in an OLSR domain
//   (i.e. a node in dual IP mode), without IP tunneling. In other words,
//   a node can either run OLSR-INRIA in IPv4 mode or IPv6 mode. But not both.
// + Link Layer notification
// + Advanced Link sensing
// + Redundant topology
// + Redundant MPR flooding

// ASSUMPTIONS ::
// + Every OLSR control packet issued by QualNet’s OLSR implementation
//   contains only one type of control message.
// + The interface address
//   with the lowest index participating inside the OLSR-MANET is
//   considered to be the main address for the node.



// STANDARD :: Coding standard follows the following Coding Guidelines
//             1. SNT C Coding Guidelines for QualNet 3.2

// **/

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <limits.h>

//Peter Modified for debug
//#include "windows.h"

//Peter Add for debug
#define DEBUG_NODE_ID 0
#define DEBUG_ENTRY_ID 34


#define INFO_SIZE 2048
#define RT_SIZE (24 * INFO_SIZE)

#define RT_SIZE_THIN (16 * INFO_SIZE)

#define MAX_PATH 260
#define ZeroMemory(Destination,Length) memset((Destination),0,(Length))
#define max(x, y) (((x) < (y)) ? (y) : (x))
#define min(a,b)    (((a) < (b)) ? (a) : (b))


#include "api.h"
#include "app_util.h"
#include "network_ip.h"

#include "ipv6.h"

#include "routing_olsr-inria.h"

//Modified by Peter
#define DEBUG          0
#define DEBUG_OUTPUT   1

//Modified by Peter to support disjoint path
#define _OLSR_DISJOINTPATH
#define DISJOINT_APPLY_THRESHOLD 4

//total final routers number for every destination
#define _OLSR_ROUTES_LIMIT 2


//temperary router number limitation during algorithm early phase
#define _OLSR_TEMP_ROUTES_LIMIT 5
//#define _OLSR_TEMP_2HOP_ROUTES_LIMIT 5

#define MAX_DIFFEERENT_ROUTE_HOP_COUNT_DIFFERENCE 8
#define MAX_DIFFEERENT_ROUTE_HOP_COUNT_DIFFERENCE_TIMES 1.5

#define MAX_COST 9999

//Peter Added to support symmetric topologylasttable

//SYMMETRIC TOPOLOGY TABLE

extern int SYMMETRIC_TOPOLOGY_TABLE;

//for debug
int g_iSymmetricDifferentCode = 1;
int g_iTopologyTableUpdateCount = 1;

//Peter Add: for same route support

int g_iToAchieveSameRoute = 1;

enum RouteEntryType
{ 
	NOT_ALLOWED, 
	//ALLOWED_BUT_NOT_TO_WORKING_SET, 
	ALLOWED_NORMAL
};


extern int OLSR_FORWARDIND_PATH_DEBUG_TRACE;

extern int FORWARD_WITH_PURE_ROUTE_TABLE;

// Peter Modified and added to suppoer olsr multipath
extern int _OLSR_MULTIPATH;

extern int _TEST_TIME_COMPLEXITY;

int g_iSimplifiedTimeTest = 1;

int g_iTestRCSimAndRealTime = 0;

extern char * g_szOutputRouteChaseFileName;

int g_iSpecailDebug = 0;

int g_iRunTimeCompare = 0;

int g_iChaseRouteTable = 0;
int g_iChaseRouteTableSkipRouteLast = 1;


int g_iNeighborChangeCnt = -1;
int g_iTopologyChangeCnt = -1;
int g_iBothChg = -1;

//for neighbor chg
int g_iNeighborChgByOlsrInsertMidAlias = -1;
//int g_iNeighborChgByOlsrUpdateNeighborStatus = -1;
int g_iNeighborChgByOlsrTimeoutLinkEntry = -1;
int g_iNeighborChgByOlsrTimeout2HopNeighbors = -1;
int g_iNeighborChgByOlsrProcessNeighborsInHelloMsg = -1;
int g_iNeighborChgByOlsrProcessReceivedHello = -1;



//for topology chg

int g_iTopologyChgByOlsrInsertMidAlias = -1;
int g_iTopologyChgByOlsrUpdateHnaEntry = -1;
//int g_iTopologyChgByOlsrUpdateNeighborStatus = -1;
int g_iTopologyChgByOlsrTimeout2HopNeighbors = -1;
int g_iTopologyChgByOlsrUpdateLastTable = -1;
int g_iTopologyChgByOlsrTimeoutTopologyTable = -1;
int g_iTopologyChgByOlsrProcessNeighborsInHelloMsg = -1;
int g_iTopologyChgByOlsrProcessReceivedHello = -1;
int g_iTopologyChgByOlsrProcessReceivedMid = -1;
int g_iTopologyChgByOlsrProcessReceivedTc = -1;

int g_iTopologyChgByOlsrProcessReceivedTcAddNew = -1;
int g_iTopologyChgByOlsrProcessReceivedTcDeleteOld = -1;

int g_iTopologyChgApplyARC = -1;

int g_iNeighborhoodChgApplyARC = -1;

int g_iTopologyChgApplyNormal = -1;

int g_iTopologyChgApplyARC_With_Delete = -1;
int g_iTopologyChgApplyARC_With_Delete_Success = -1;
int g_iTopologyChgApplyARC_With_Delete_Failed_Cause_Rediscovery = -1;

extern int  g_OverallipOutNoRoutes;

char g_szText[4096];


//char g_szTextRTPre[16384];

//char g_szTextRTMiddle[16384];

char g_szTextRT[16384];




/*
int NODE_ID_FOR_TEST_OUTER_ANGLE = 1 ;
int NODE_ID_FOR_TEST_OUTER_EDGE = 19 ;
int NODE_ID_FOR_TEST_MIDDLE_ANGLE = 8 ;
int NODE_ID_FOR_TEST_MIDDLE_EDGE = 10 ;
int NODE_ID_FOR_TEST_CENTER = 16 ;
*/

int NODE_ID_FOR_TEST_START = 0;
int NODE_ID_FOR_TEST_END = 0;
char * g_szRoot = NULL;


int g_iKeepOrder = 1;

//#define File_Buf_Size  1024 * 1024 * 100
//char * g_strTxt = NULL;


#define VALID_SIMULATE_CHECK_TIME -1


extern int g_iAccumulativeRouteCalculation;
int g_iMobilitySpeed = 0;



//Peter added

int CmpBreakPoint(Node *node)
{

	

	//char szTextRT[MAX_STRING_LENGTH];
	

	char timeStr[MAX_STRING_LENGTH];
	TIME_PrintClockInSecond(getSimTime(node), timeStr, node);

	double dSimTime = atof(timeStr);



	RoutingOlsr* olsr = (RoutingOlsr *) node->appData.olsr;


	int iNeighborChg = 0;

	if (olsr->changes_neighborhood)
	{
		iNeighborChg = 1;
	}

	int iRTAddOrDelete = 0;
	if (olsr->recent_add_list != NULL)
	{
		iRTAddOrDelete = iRTAddOrDelete + 1;
	}

	if (olsr->recent_delete_list != NULL)
	{

		iRTAddOrDelete = iRTAddOrDelete + 2;
	}

	
	if (olsr->pszInfo != NULL)
	{
		memset(olsr->pszInfo, 0, INFO_SIZE * sizeof(char));
	
	
		//RoutingOlsr* olsr = (RoutingOlsr *) node->appData.olsr;

		tco_node_addr * tco_add_list_tmp = olsr->recent_add_list;


		sprintf(olsr->pszInfo, "For node->nodeId = %d, iRTAddOrDelete = %d, olsr->naRecentChangedAddressByTC = %d, iNeighborChg = %d, olsr->bNeighborChgCausedRemoveFromHigherHop = %d, at time %f S: \n", 
			node->nodeId, iRTAddOrDelete, olsr->naRecentChangedAddressByTC, iNeighborChg, olsr->bNeighborChgCausedRemoveFromHigherHop, dSimTime);


		sprintf(olsr->pszInfo, "%sadd_list: ", olsr->pszInfo);

		while (tco_add_list_tmp != NULL)
		{

			sprintf(olsr->pszInfo, "%s %d;  ", olsr->pszInfo, tco_add_list_tmp->nid);

			tco_add_list_tmp = tco_add_list_tmp->next;
		}

		sprintf(olsr->pszInfo, "%s\n", olsr->pszInfo);

		tco_node_addr * tco_delete_list_tmp = olsr->recent_delete_list;



		sprintf(olsr->pszInfo, "%sdelete_list: ", olsr->pszInfo);

		while (tco_delete_list_tmp != NULL)
		{

			sprintf(olsr->pszInfo, "%s %d;  ", olsr->pszInfo, tco_delete_list_tmp->nid);

			tco_delete_list_tmp = tco_delete_list_tmp->next;
		}
	}
	

	

	if (node->nodeId == DEBUG_NODE_ID && iRTAddOrDelete == 2 && olsr->naRecentChangedAddressByTC == 23 && iNeighborChg == 0 
		&& olsr->bNeighborChgCausedRemoveFromHigherHop == 0 && dSimTime > 14 && dSimTime < 16)
	{
		//DebugBreak();
		int i = 0;
		i = i + 2;

		//g_iSpecailDebug = 1;

		//g_iRunTimeCompare = 1;


	}
	else
	{
		//g_iSpecailDebug = 0;
	}

	



	return iRTAddOrDelete;
}

void PUSH_BACK_CURRENT_ITEM(RoutingOlsr *olsr, tc_trace_item tti)
{
	olsr->iTcItemCnt++;
	if (olsr->iTcItemCnt > olsr->iTcItemSize)
	{
		//reallocate memory
		int iNewSize = olsr->iTcItemSize * 2;
		tc_trace_item * ptti = new tc_trace_item[iNewSize];
		memset(ptti, 0, iNewSize * sizeof(tc_trace_item));
		memcpy(ptti, olsr->pvt_TTIs, olsr->iTcItemSize * sizeof(tc_trace_item));
		delete [] olsr->pvt_TTIs;
		olsr->pvt_TTIs = ptti;
		olsr->iTcItemSize = iNewSize;
	}
	memcpy(&(olsr->pvt_TTIs[olsr->iTcItemCnt - 1]), &tti, sizeof(tc_trace_item));
}




//bool is_in_tco_node_addr_set(tco_node_addr * tna_set, NodeAddress nodeId)

void insert_into_tco_node_addr_set(tco_node_addr ** ptna_set, NodeAddress nodeId)
{
	tco_node_addr * node_addr_new;

	
	if (*ptna_set == NULL)
	{
		//tna_set = node_addr_new;
		*ptna_set = (tco_node_addr *)MEM_malloc(sizeof(tco_node_addr));
		memset(*ptna_set, 0, sizeof(tco_node_addr));

		(*ptna_set)->nid = nodeId;
		(*ptna_set)->next = NULL;

	}
	else
	{

		node_addr_new = (tco_node_addr *)MEM_malloc(sizeof(tco_node_addr));
		memset(node_addr_new, 0, sizeof(tco_node_addr));

		node_addr_new->nid = nodeId;
		node_addr_new->next = NULL;

		node_addr_new->next = (*ptna_set)->next;
		(*ptna_set)->next = node_addr_new;
	}

	
	
}

bool remove_from_tco_node_addr_set(tco_node_addr ** ptna_set, NodeAddress nodeId)
{
	bool bExist = false;
	
	tco_node_addr* dest_list;
    tco_node_addr* dest_list_tmp;

    
    dest_list = *ptna_set;
    *ptna_set = NULL;

    while (dest_list != NULL)
    {
		if (dest_list->nid == nodeId)
        {
            // address matches, remove from the destination list
            dest_list_tmp = dest_list;
            dest_list = dest_list->next;
            MEM_free(dest_list_tmp);

			bExist = true;
        }
        else
        {
            dest_list_tmp = dest_list;
            dest_list = dest_list->next;
            dest_list_tmp->next = *ptna_set;
            *ptna_set = dest_list_tmp;
        }
    }

	return bExist;

}


bool exist_in_tco_node_addr_set(tco_node_addr ** ptna_set, NodeAddress nodeId)
{
	bool bExist = false;

	tco_node_addr* dest_list = NULL;
	//tco_node_addr* dest_list_tmp;


	dest_list = *ptna_set;
	//*ptna_set = NULL;

	while (dest_list != NULL)
	{
				
		if (dest_list->nid == nodeId)
		{
			

			bExist = true;
			break;
		}

		dest_list = dest_list->next;
	
	}

	return bExist;

}



void clear_tco_node_addr_set(tco_node_addr ** ptna_set)
{
	
    tco_node_addr* node_addr_set_tmp;

    while ((*ptna_set) != NULL)
    {

		//DebugBreak();

        node_addr_set_tmp = (*ptna_set);
        (*ptna_set) = (*ptna_set)->next;
        MEM_free(node_addr_set_tmp);
    }
}

//Peter Modified for disjoint path
//_OLSR_DISJOINTPATH
static
void OLSRv1UpdateForwardingTableWithDisjointPath(Node *node, rt_entry* prte)
{


	if (prte->rt_dst.networkType == NETWORK_IPV6)
	{

		/*
		Ipv6UpdateForwardingTable(
		node,
		GetIPv6Address(prte->rt_dst),
		128,
		GetIPv6Address(prte->rt_router),
		prte->rt_interface,
		prte->rt_metric,
		ROUTING_PROTOCOL_OLSR_INRIA);
		*/

	}
	else
	{

                double dDgrWRT = 0.0;
                double dDtsWRT = 0.0; 

                if (_TEST_TIME_COMPLEXITY)
                {
                     dDgrWRT = prte->rt_entry_infos.related_neighbor->neighbor_infos.dDegreeWRTNode;
                     dDtsWRT = prte->rt_entry_infos.related_neighbor->neighbor_infos.dDistanceWRTNode;
                }
                else
                {
                     dDgrWRT = prte->rt_entry_infos.rtu_DegreeWRTNode;
                     dDtsWRT = prte->rt_entry_infos.rtu_DistanceWRTNode;
                }

                

		NetworkUpdateForwardingTableWithDisjointPath(
			node,
			GetIPv4Address(prte->rt_dst),
			0xffffffff,
			GetIPv4Address(prte->rt_router),
			prte->rt_interface,
			prte->rt_metric,
			ROUTING_PROTOCOL_OLSR_INRIA,
			dDgrWRT,
			dDtsWRT
                        );
	}


}

// /**
// FUNCTION   ::  OlsrLookup2HopNeighborTable
// LAYER      :: APPLICATION
// PURPOSE    :: Searches an address in the two hop neighbor table
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + dest : Address: address to be searched
// RETURN :: neighbor_2_entry* : Pointer to entry if found, else NULL
// **/
neighbor_2_entry*
OlsrLookup2HopNeighborTable(
    Node* node,
    Address dest);

// /**
// FUNCTION   :: OlsrDelete2HopNeighborTable
// LAYER      :: APPLICATION
// PURPOSE    :: Delete a two hop neighbor entry results the deletion of
//               its 1 hop neighbors list. We don't try to remove the one
//               hop neighbor even if it has no more 2 hop neighbors.
// PARAMETERS ::
// + two_hop_neighbor : neighbor_2_entry* : Pointer to two hop neighbor entry
// RETURN :: void : NULL
// **/
void OlsrDelete2HopNeighborTable(
    neighbor_2_entry* two_hop_neighbor);

// /**
// FUNCTION   :: OlsrLookupNeighborTable
// LAYER      :: APPLICATION
// PURPOSE    :: Searches neighbor table for this address
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + dst : Address: Address to look for
// RETURN :: neighbor_entry * : if found, pointer to entry
//                              else NULL
// **/
neighbor_entry* OlsrLookupNeighborTable(
    Node* node,
    Address dst);

// /**
// FUNCTION   :: OlsrInsertNeighborTable
// LAYER      :: APPLICATION
// PURPOSE    :: Inserts neighbor entry in the neighbor table
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + neighbor: neighbor_entry * : entry to be inserted
// RETURN :: void : NULL
// **/
void OlsrInsertNeighborTable(
    Node* node,
    neighbor_entry* neighbor);

// /**
// FUNCTION   :: OlsrDeleteNeighbor2Pointer
// LAYER      :: APPLICATION
// PURPOSE    :: Deletes current address from the 2 hop neighbor list of this
//               neighbor entry
// PARAMETERS ::
// + neighbor : neighbor_entry* : Pointer to neighbor entry
// + address : Address : Address to be deleted from two hop neighbor list
// RETURN :: void : NULL
// **/
void OlsrDeleteNeighbor2Pointer(
    neighbor_entry* neighbor,
    Address address);

// /**
// FUNCTION   :: OlsrDeleteNeighborTable
// LAYER      :: APPLICATION
// PURPOSE    :: Deletes current neighbor entry from the neighbor table
// PARAMETERS ::
// + neighbor : neighbor_entry* : Pointer to entry to be deleted
// RETURN :: void : NULL
// **/
void OlsrDeleteNeighborTable(
    neighbor_entry* neighbor);

// /**
// FUNCTION   :: OlsrForwardMessage
// LAYER      :: APPLICATION
// PURPOSE    :: Check if a message is to be forwarded and forward
//               it if necessary.
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + m : olsrmsg * : Pointer to message
// + originator: Address: originator of message
// + seqno : UInt16 : seq no of message
// + interfaceIndex : Int32: interface that packet arrived on
// + from_addr : Address: Neighbor Interface address that transmitted msg
// RETURN :: Int32 : 1 if msg is sent to be fwded, 0 if not
// **/
Int32 OlsrForwardMessage(
    Node* node,
    olsrmsg* m,
    Address originator,
    UInt16 seqno,
    Int32 interfaceIndex,
    Address from_addr);

// /**
// FUNCTION   :: RoutingOlsrCheckMyIfaceAddress
// LAYER      :: APPLICATION
// PURPOSE    :: Function checks if address is not one of the
//               current node's interface address
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + addr : Address: Address to be checked
// RETURN :: Int32 : Returns interface index if match, else -1
// **/
Int32 RoutingOlsrCheckMyIfaceAddress(
    Node* node,
    Address addr);

// /**
// FUNCTION   :: OlsrLookupMprSelectorTable
// LAYER      :: APPLICATION
// PURPOSE    :: Search an address in the MPR  selector table
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + dst  : Address : Address to be searched
// RETURN :: mpr_selector_entry* : Pointer to entry if found, else NULL
// **/
mpr_selector_entry* OlsrLookupMprSelectorTable(
    Node* node,
    Address addr);

// /**
// FUNCTION   :: OlsrDeleteMprSelectorTable
// LAYER      :: APPLICATION
// PURPOSE    :: Deletes entry from MPR  selector table
// PARAMETERS ::
// + mprs : mpr_selector_entry *: Pointer to mpr entry
// RETURN :: void : NULL
// **/
void OlsrDeleteMprSelectorTable(
    mpr_selector_entry* mprs);

/***************************************************************************
 *                    Definition of List Management                        *
 ***************************************************************************/

// /**
// FUNCTION   :: OlsrInsertList
// LAYER      :: APPLICATION
// PURPOSE    :: Inserts in the list
// PARAMETERS ::
// + elem : ols_qelem* : Pointer to element
// + prev : ols_qelem* : Pointer to previous element
// RETURN :: void : NULL
// **/

static
void OlsrInsertList(
    olsr_qelem* elem,
    olsr_qelem* prev)
{
    elem->q_back = prev;
    elem->q_forw = (olsr_qelem *)prev->q_forw;
    prev->q_forw = elem;
    ((olsr_qelem *) elem->q_forw)->q_back = elem;
}


// /**
// FUNCTION   :: OlsrRemoveList
// LAYER      :: APPLICATION
// PURPOSE    :: Removes from  the list
// PARAMETERS ::
// + elem : ols_qelem* : Pointer to element
// RETURN :: void : NULL
// **/

static
void OlsrRemoveList(
    olsr_qelem* elem)
{
    ((olsr_qelem *) elem->q_back)->q_forw = (olsr_qelem *)elem->q_forw;
    ((olsr_qelem *) elem->q_forw)->q_back = (olsr_qelem *)elem->q_back;
}


// /**
// FUNCTION   :: OlsrHashing
// LAYER      :: APPLICATION
// PURPOSE    :: Returns hash value
// PARAMETERS ::
// + address      : Address : Address of node
// + h : UInt32*  : returned hash value
// RETURN :: void : NULL
// **/

static
void OlsrHashing(
    Address address,
    UInt32* h)
{
    UInt32 hash = 0;

    if (address.networkType == NETWORK_IPV6)
    {
        unsigned int byte = 0;

        byte = address.interfaceAddr.ipv6.s6_addr[12];
        hash |= (byte << 24);

        byte = address.interfaceAddr.ipv6.s6_addr[13];
        hash |= (byte << 16);

        byte = address.interfaceAddr.ipv6.s6_addr[14];
        hash |= (byte << 8);

        byte = address.interfaceAddr.ipv6.s6_addr[15];
        hash |= byte;
    }
    else

    {
        hash = GetIPv4Address(address);
    }
    *h = hash;
}


// /**
// FUNCTION   :: OlsrDouble2ME
// LAYER      :: APPLICATION
// PURPOSE    :: Converts a Float32 to mantissa/exponent
//               format as per RFC 3626
// PARAMETERS ::
// + interval : Float32 : value to be converted
// RETURN :: unsigned char : 8 bit mantissa/exponent product
// **/

static
unsigned char OlsrDouble2ME(
    Float32 interval)
{
    // Section 18.3 RFC 3626
    Int32 a;
    Int32 b;

    b = 0;
    while (interval / VTIME_SCALE_FACTOR >= pow((Float32)2, (Float32)b))
    {
        b++;
    }
    b--;
    if (b < 0)
    {
        a = 1;
        b = 0;
    }
    else if (b > 15)
    {
        a = 15;
        b = 15;
    }
    else
    {
        a = (Int32)(16 * ((Float32)interval /
                       (VTIME_SCALE_FACTOR * (Float32)pow((double)2, b)) - 1));
        while (a >= 16)
        {
            a -= 16;
            b++;
        }
    }
    unsigned char value;
    value = (unsigned char) (a * 16 + b);
    return value;
}


// /**
// FUNCTION   :: OlsrME2Double
// LAYER      :: APPLICATION
// PURPOSE    :: Converts a mantissa/exponent
//               format  to Float32 as per RFC 3626
// PARAMETERS ::
// + me : unsigned char : 8 bit m/e value to be converted
// RETURN :: Float32 : returns 32-bit value
// **/

static
Float32 OlsrME2Double(
    unsigned char me)
{
    // Section 18.3 RFC 3626
    Int32 a;
    Int32 b;

    a = me >> 4;
    b = me - a * 16;

    return (Float32)(VTIME_SCALE_FACTOR * (1 + (Float32)a / 16)
                   * (Float32)pow((double)2, b));
}


// /**
// FUNCTION   :: OlsrGetMsgSeqNo
// LAYER      :: APPLICATION
// PURPOSE    :: Returns current message sequence counter
//               and increments the counter
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// RETURN :: short : Message sequence number
// **/

static
Int16 OlsrGetMsgSeqNo(
    Node* node)
{
    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;
    return olsr->message_seqno++;
}


//*************************************************************************//
//                          MID Table Handling                             //
//*************************************************************************//

// /**
// FUNCTION   :: OlsrMidLookupMainAddr
// LAYER      :: APPLICATION
// PURPOSE    :: Returns main_address given an alias
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + alias : Address : alias address
// RETURN :: Address : main address of the alias
// **/

static
Address OlsrMidLookupMainAddr(
    Node* node,
    Address alias)
{
    UInt32 alias_addr_hash;
    mid_alias_hash_type* hash_mid_alias;
    mid_address* curr_mid_addr;
    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    OlsrHashing(alias, &alias_addr_hash);

    hash_mid_alias = &olsr->midtable.mid_alias_hash[alias_addr_hash
                                                    % HASHMASK];
    for (curr_mid_addr = hash_mid_alias->mid_forw;
         curr_mid_addr != (mid_address* )hash_mid_alias;
         curr_mid_addr = curr_mid_addr->next)
    {
        if (Address_IsSameAddress(&(curr_mid_addr->alias), &alias))
        {
            return curr_mid_addr->main_entry->mid_infos.main_addr;
        }
    }

    Address any_addr;
    Address_SetToAnyAddress(&any_addr, &alias);
    return any_addr;
}


// /**
// FUNCTION   :: OlsrLookupMidAliases
// LAYER      :: APPLICATION
// PURPOSE    :: Returns a link list of aliases for a given main_address
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + main_addr :    Address : main_address
// RETURN :: mid_address* : link list of aliases of the given main_address
// **/

static
mid_address* OlsrLookupMidAliases(
    Node* node,
    Address main_addr)
{
    UInt32 main_addr_hash;
    mid_main_hash_type* hash_mid_main;
    mid_entry* curr_mid_entry;
    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    OlsrHashing(main_addr, &main_addr_hash);

    hash_mid_main = &olsr->midtable.mid_main_hash[main_addr_hash % HASHMASK];

    for (curr_mid_entry = hash_mid_main->mid_forw;
         curr_mid_entry != (mid_entry *)hash_mid_main;
         curr_mid_entry = curr_mid_entry->mid_forw)
    {
        if (Address_IsSameAddress(&curr_mid_entry->mid_infos.main_addr,
                &main_addr))
        {
            return curr_mid_entry->mid_infos.aliases;
        }
    }
    return NULL;
}

// /**
// FUNCTION   :: OlsrInsertMidTable
// LAYER      :: APPLICATION
// PURPOSE    :: Insert an alias entry into the MID table
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + main_addr : Address : Main address of an olsr-node
// + alias : mid_address* : alias entry
// + vtime : Float32 : Validity time
// RETURN :: void : NULL
// **/
static
void OlsrInsertMidTable(
    Node* node,
    Address main_addr,
    mid_address* alias,
    Float32 vtime)
{
    UInt32 alias_addr_hash;
    UInt32 main_addr_hash;
    mid_main_hash_type* hash_mid_main;
    mid_alias_hash_type* hash_mid_alias;
    mid_entry* curr_mid_entry;
    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    OlsrHashing(main_addr, &main_addr_hash);
    OlsrHashing(alias->alias, &alias_addr_hash);

    hash_mid_main = &olsr->midtable.mid_main_hash[main_addr_hash % HASHMASK];
    hash_mid_alias = &olsr->midtable.mid_alias_hash[alias_addr_hash
                                                    % HASHMASK];

    for (curr_mid_entry = hash_mid_main->mid_forw;
         curr_mid_entry != (mid_entry *)hash_mid_main;
         curr_mid_entry = curr_mid_entry->mid_forw)
    {
        if (Address_IsSameAddress(&curr_mid_entry->mid_infos.main_addr,
                &main_addr))
        {
            break;
        }
    }

    if (curr_mid_entry != (mid_entry* )hash_mid_main)
    {
        alias->next_alias = curr_mid_entry->mid_infos.aliases;
    }
    else
    {
        curr_mid_entry = (mid_entry* )MEM_malloc(sizeof(mid_entry));
        memset(curr_mid_entry, 0, sizeof(mid_entry));
        OlsrInsertList((olsr_qelem* )curr_mid_entry,
            (olsr_qelem* )hash_mid_main);

        curr_mid_entry->mid_infos.main_addr = main_addr;
        alias->next_alias = NULL;
    }

    curr_mid_entry->mid_infos.aliases = alias;
    alias->main_entry = curr_mid_entry;
    curr_mid_entry->mid_infos.mid_timer = getSimTime(node)
                                          + (clocktype)(vtime * SECOND);
    OlsrInsertList((olsr_qelem* )alias, (olsr_qelem* )hash_mid_alias);

    return;
}

// /**
// FUNCTION   :: OlsrInsertMidAlias
// LAYER      :: APPLICATION
// PURPOSE    :: Insert alias address into MID table
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + main_address : Address : main address
// + alias : Address : alias address
// + vtime : Float32 : Validity time
// RETURN :: void : NULL
// **/
static
void OlsrInsertMidAlias(
    Node* node,
    Address main_address,
    Address alias,
    Float32 vtime)
{
    mid_address* mid_alias = (mid_address* )MEM_malloc(sizeof(mid_address));
    memset(mid_alias, 0, sizeof(mid_address));

    mid_alias->alias = alias;
    mid_alias->next_alias = NULL;

    OlsrInsertMidTable(node, main_address, mid_alias, vtime);

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;
    olsr->changes_topology = TRUE;
    
	//Peter Comment: will never be called under current simulation setting that only one interface for one node
	
	olsr->changes_neighborhood = TRUE;

	g_iNeighborChgByOlsrInsertMidAlias++;
	g_iTopologyChgByOlsrInsertMidAlias++;

    return;
}


// /**
// FUNCTION   :: OlsrDeleteMidTable
// LAYER      :: APPLICATION
// PURPOSE    :: Delete a MID table entry
// PARAMETERS ::
// + entry : mid_entry* : Pointer to MID table entry
// RETURN :: void : NULL
// **/
static
void OlsrDeleteMidTable(
    mid_entry* entry)
{
    mid_address *aliases;

    // Free aliases
    aliases = entry->mid_infos.aliases;
    while (aliases)
    {
        mid_address *tmp_aliases = aliases;
        aliases = aliases->next_alias;
        OlsrRemoveList((olsr_qelem *) tmp_aliases);
        free(tmp_aliases);
    }
    OlsrRemoveList((olsr_qelem *)entry);
    free(entry);

    return;
}

// /**
// FUNCTION   :: OlsrTimeoutMidTable
// LAYER      :: APPLICATION
// PURPOSE    :: Check MID table entry for time out
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// RETURN :: void : NULL
// **/
static
void OlsrTimeoutMidTable(
    Node* node)
{
    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;
    unsigned char index;
    for (index = 0; index < HASHSIZE; index++)
    {
        mid_entry* tmp_list = olsr->midtable.mid_main_hash[index].mid_forw;

        // Traverse MID list
        while (tmp_list != (mid_entry* )&olsr->midtable.mid_main_hash[index])
        {
            if (getSimTime(node) >= tmp_list->mid_infos.mid_timer)
            {
                mid_entry* entry_to_delete = tmp_list;
                tmp_list = tmp_list->mid_forw;

                if (DEBUG)
                {
                    char addrString[MAX_STRING_LENGTH];
                    IO_ConvertIpAddressToString(
                        &entry_to_delete->mid_infos.main_addr,
                        addrString);
                    printf("Node %u: Deleting MID table entry "
                           "for main address %s\n",
                        node->nodeId,
                        addrString);
                }
                OlsrDeleteMidTable(entry_to_delete);
            }
            else
            {
                tmp_list = tmp_list->mid_forw;
            }
        }
    }

    return;
}

// /**
// FUNCTION   :: OlsrUpdateMidTable
// LAYER      :: APPLICATION
// PURPOSE    :: Update timer of a MID table entry
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + main_addr : Address : Main address of an olsr-node
// + vtime : Float32 : Validity time
// RETURN :: void : NULL
// **/
static
void OlsrUpdateMidTable(
    Node* node,
    Address main_addr,
    Float32 vtime)
{
    UInt32 main_addr_hash;
    mid_main_hash_type* hash_mid_main;
    mid_entry* curr_mid_entry;

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;
    OlsrHashing(main_addr, &main_addr_hash);

    hash_mid_main = &olsr->midtable.mid_main_hash[main_addr_hash % HASHMASK];

    for (curr_mid_entry = hash_mid_main->mid_forw;
         curr_mid_entry != (mid_entry *)hash_mid_main;
         curr_mid_entry = curr_mid_entry->mid_forw)
    {
        if (Address_IsSameAddress(&curr_mid_entry->mid_infos.main_addr,
                &main_addr))
        {
            curr_mid_entry->mid_infos.mid_timer =
                getSimTime(node) + (clocktype)(vtime * SECOND);
            return;
        }
    }
    return;
}

// /**
// FUNCTION   :: OlsrPrintMidTable
// LAYER      :: APPLICATION
// PURPOSE    :: Print MID table of an olsr node
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// RETURN :: void : NULL
// **/
static
void OlsrPrintMidTable(
    Node* node)
{
    unsigned char index;
    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;
    char addrString[MAX_STRING_LENGTH];


    printf("\nMID table for Node:%u\n", node->nodeId);

    for (index = 0; index < HASHSIZE; index++)
    {
        mid_entry *tmp_list = olsr->midtable.mid_main_hash[index].mid_forw;

        // Traverse MID list
        for (tmp_list = olsr->midtable.mid_main_hash[index].mid_forw;
            tmp_list != (mid_entry* )&olsr->midtable.mid_main_hash[index];
            tmp_list = tmp_list->mid_forw)
        {
            mid_address* tmp_addr = tmp_list->mid_infos.aliases;

            IO_ConvertIpAddressToString(&tmp_list->mid_infos.main_addr,
                addrString);
            printf("%s(Main Address) : ", addrString);
            printf("[Alias Addresses : ");

            while (tmp_addr)
            {
                IO_ConvertIpAddressToString(&tmp_addr->alias, addrString);
                printf("%s ", addrString);

                tmp_addr = tmp_addr->next_alias;
            }
            printf("]\n");
        }
    }
    return;
}

//*************************************************************************//
//                         HNA Table Handling
//*************************************************************************//

// /**
// FUNCTION   :: OlsrLookupHnaNet
// LAYER      :: APPLICATION
// PURPOSE    :: Looks up HNA table for a given net address
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + nets : hna_net* : pointer to the network list to look in
// + net  : Address : The network to look for
// + mask : hna_netmask : The netmask to look for
// RETURN :: hna_net* : pointer to the entry or NULL if not found
// **/
hna_net* OlsrLookupHnaNet(
    Node* node,
    hna_net* nets,
    Address net,
    hna_netmask mask)
{
  hna_net* tmp_net;

  // Loop trough entrys
  for (tmp_net = nets->next;
      tmp_net != nets;
      tmp_net = tmp_net->next)
  {
      if (Address_IsSameAddress(&tmp_net->A_network_addr, &net)
          && ((net.networkType == NETWORK_IPV6
               && tmp_net->A_netmask.v6 == mask.v6)
             || (net.networkType == NETWORK_IPV4
                 && tmp_net->A_netmask.v4 == mask.v4)))
      {

          return tmp_net;
      }
  }

  // Not found
  return NULL;
}

// /**
// FUNCTION   :: OlsrLookupHnaGateway
// LAYER      :: APPLICATION
// PURPOSE    :: Looks up HNA table for a given a gateway entry
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + gw   : Address : The gateway address
// RETURN :: hna_entry* : pointer to the entry or NULL if not found
// **/
hna_entry* OlsrLookupHnaGateway(
    Node* node,
    Address gw)
{
    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;
    hna_entry* tmp_hna;
    hna_entry* hash_hna_entry;
    UInt32 hash;

    OlsrHashing(gw, &hash);
    hash_hna_entry = &olsr->hna_table[hash % HASHMASK];

    // Check for registered entry
    for (tmp_hna = hash_hna_entry->next;
        tmp_hna != hash_hna_entry;
        tmp_hna = tmp_hna->next)
    {
        if (Address_IsSameAddress(&tmp_hna->A_gateway_addr, &gw))
        {
            return tmp_hna;
        }
    }

    return NULL;
}

// /**
// FUNCTION   :: OlsrAddHnaEntry
// LAYER      :: APPLICATION
// PURPOSE    :: adds gateway to HNA table
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + gw   : Address : The gateway address
// RETURN :: hna_entry* : pointer to the new entry
// **/
hna_entry* OlsrAddHnaEntry(
    Node* node,
    Address addr)
{
    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;
    hna_entry* new_entry;
    UInt32 hash;

    new_entry = (hna_entry*)MEM_malloc(sizeof(hna_entry));
    memset(new_entry, 0, sizeof(hna_entry));

    new_entry->A_gateway_addr = addr;

    // Link nets
    new_entry->networks.next = &new_entry->networks;
    new_entry->networks.prev = &new_entry->networks;

    // queue

    OlsrHashing(addr, &hash);
    hna_entry* hash_hna_entry = &olsr->hna_table[hash % HASHMASK];
    OlsrInsertList((olsr_qelem* )new_entry, (olsr_qelem* )hash_hna_entry);

    return new_entry;

}

// /**
// FUNCTION   :: OlsrAddHnaNet
// LAYER      :: APPLICATION
// PURPOSE    :: Adds a network entry to a HNA gateway
// PARAMETERS ::
// + hna_gw : hna_entry* : Pointer to the gateway to the non-olsr network
// + net  : Address : The network to add
// + mask : hna_netmask : The netmask to add
// RETURN :: hna_net* : pointer to the new entry
// **/
hna_net* OlsrAddHnaNet(
    hna_entry* hna_gw,
    Address net,
    hna_netmask mask)
{
    hna_net* new_net;

    // Add the net
    new_net = (hna_net*) MEM_malloc(sizeof(hna_net));
    memset(new_net, 0, sizeof(hna_net));

    new_net->A_network_addr = net;
    new_net->A_netmask = mask;

    // Queue
    hna_gw->networks.next->prev = new_net;
    new_net->next = hna_gw->networks.next;
    hna_gw->networks.next = new_net;
    new_net->prev = &hna_gw->networks;

    return new_net;
}

// /**
// FUNCTION   :: OlsrUpdateHnaEntry
// LAYER      :: APPLICATION
// PURPOSE    :: updates network entry in HNA table
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + gw   : Address : The gateway address
// + net  : Address : The network address
// + mask : hna_netmask : The netmask
// + vtime : Folat32 : validity time
// RETURN :: void : NULL
// **/
static
void OlsrUpdateHnaEntry(
    Node* node,
    Address gw,
    Address net,
    hna_netmask mask,
    Float32 vtime)
{
    hna_entry* gw_entry;
    hna_net* net_entry;
    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    // FIX: Skip update operation if the network is
    // directly connected to the receiving node

    for (Int32 i = 0; i < node->numberInterfaces; i++)
    {
        Address interfaceAddr;
        Address netAddr;

        if (NetworkIpGetInterfaceType(node, i) != olsr->ip_version
            && NetworkIpGetInterfaceType(node, i)!= NETWORK_DUAL)
        {
            continue;
        }

        if(olsr->ip_version == NETWORK_IPV6)
        {
            interfaceAddr.networkType = NETWORK_IPV6;
            Ipv6GetGlobalAggrAddress(
                    node,
                    i,
                    &interfaceAddr.interfaceAddr.ipv6);
        }
        else if (olsr->ip_version == NETWORK_IPV4)
        {
            interfaceAddr.networkType = NETWORK_IPV4;
            interfaceAddr.interfaceAddr.ipv4 =
                            NetworkIpGetInterfaceAddress(node,i);
        }
//#endif

        if (olsr->ip_version == NETWORK_IPV6)
        {
            Ipv6GetPrefix(&interfaceAddr.interfaceAddr.ipv6,
                &netAddr.interfaceAddr.ipv6,
                MAX_PREFIX_LEN);
            netAddr.networkType = NETWORK_IPV6;
        }
        else
        {
            UInt32 netmask = NetworkIpGetInterfaceSubnetMask(node, i);

            if (netmask)
            {
                netAddr.interfaceAddr.ipv4 =
                                interfaceAddr.interfaceAddr.ipv4 % netmask;
            }
            else
            {
                netAddr.interfaceAddr.ipv4 =
                                            interfaceAddr.interfaceAddr.ipv4;
            }
            netAddr.networkType = NETWORK_IPV4;
        }

        if (Address_IsSameAddress(&netAddr, &net))
        {
            return;
        }
    }

    if ((gw_entry = OlsrLookupHnaGateway(node, gw)) == NULL)
    {
        // Need to add the entry
        gw_entry = OlsrAddHnaEntry(node, gw);

        if (DEBUG)
        {
            printf("Node %u : Adding HNA GW entry\n", node->nodeId);
        }
    }

    if ((net_entry = OlsrLookupHnaNet(node,
                        &gw_entry->networks, net, mask)) == NULL)
    {
        // Need to add the net
        net_entry = OlsrAddHnaNet(gw_entry, net, mask);
        olsr->changes_topology = TRUE;

	g_iTopologyChgByOlsrUpdateHnaEntry++;

        if (DEBUG)
        {
            printf("Node %u : Adding HNA entry\n", node->nodeId);
        }
    }

    // Update holdingtime
    net_entry->A_time = getSimTime(node) + (clocktype)(vtime * SECOND);

}

// /**
// FUNCTION   :: OlsrTimeoutHnaTable
// LAYER      :: APPLICATION
// PURPOSE    :: times out all the old entries in the hna table
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// RETURN :: void : NULL
// **/
static
void OlsrTimeoutHnaTable(
    Node* node)
{
    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;
    unsigned char index;

    for (index = 0; index < HASHSIZE; index++)
    {
        hna_entry* tmp_hna = olsr->hna_table[index].next;
        // Check all entrys
        while (tmp_hna != &olsr->hna_table[index])
        {
            // Check all networks
            hna_net* tmp_net = tmp_hna->networks.next;

            while (tmp_net != &tmp_hna->networks)
            {
                if (getSimTime(node) >= tmp_net->A_time)
                {
                    hna_net* net_to_delete = tmp_net;
                    tmp_net = tmp_net->next;
                    OlsrRemoveList((olsr_qelem *) net_to_delete);
                    MEM_free(net_to_delete);
                }
                else
                {
                    tmp_net = tmp_net->next;
                }
            }

            // Delete gw entry if empty
            if (tmp_hna->networks.next == &tmp_hna->networks)
            {
                hna_entry* hna_to_delete = tmp_hna;
                tmp_hna = tmp_hna->next;

                // Dequeue
                OlsrRemoveList((olsr_qelem *)hna_to_delete);
                // Delete
                MEM_free(hna_to_delete);
            }
            else
            {
                tmp_hna = tmp_hna->next;
            }
        }
    }
}

// /**
// FUNCTION   :: OlsrPrintHnaTable
// LAYER      :: APPLICATION
// PURPOSE    :: print all the entries in the hna table
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// RETURN :: void : NULL
// **/
static
void OlsrPrintHnaTable(Node* node)
{
    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    unsigned char index;
    char addrString[MAX_STRING_LENGTH];

    printf("HNA Table for Node %u\n",node->nodeId);
    if (olsr->ip_version == NETWORK_IPV6)
    {
        printf("IP net /prefixlen               GW-IP\n");
    }
    else
    {
        printf("IP net          netmask         GW-IP\n");
    }

    for (index = 0; index < HASHSIZE; index++)
    {
        hna_entry* tmp_hna = olsr->hna_table[index].next;
        // Check all entrys
        while (tmp_hna != &olsr->hna_table[index])
        {
            // Check all networks
            hna_net* tmp_net = tmp_hna->networks.next;

            while (tmp_net != &tmp_hna->networks)
            {
                IO_ConvertIpAddressToString(&tmp_net->A_network_addr,
                    addrString);

                if (olsr->ip_version == NETWORK_IPV6)
                {
                    printf("%-27s", addrString);
                    printf("/%d", tmp_net->A_netmask.v6);

                    IO_ConvertIpAddressToString(&tmp_hna->A_gateway_addr,
                        addrString);
                    printf(" %s\n", addrString);
                }
                else
                {
                    printf("%-15s ", addrString);
                    IO_ConvertIpAddressToString(tmp_net->A_netmask.v4,
                        addrString);
                    printf("%-15s ", addrString);
                    IO_ConvertIpAddressToString(&(tmp_hna->A_gateway_addr),
                        addrString);
                    printf("%-15s\n", addrString);
                }

                tmp_net = tmp_net->next;
            }
            tmp_hna = tmp_hna->next;
        }
    }
}

//*************************************************************************//
//                    Link Sensing Table Handling
//*************************************************************************//

// /**
// FUNCTION   :: OlsrLookupLinkStatus
// LAYER      :: APPLICATION
// PURPOSE    :: Looks up status of entry based on the timer entries
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + entry : link_entry* : Pointer to link set entry
// RETURN :: Int32 : status of link
// **/

static
Int32 OlsrLookupLinkStatus(
    Node* node,
    link_entry* entry)
{

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    if (entry == NULL || olsr->link_set == NULL)
    {
        return UNSPEC_LINK;
    }

    clocktype curr_time = getSimTime(node);

    // RFC 3626 Section 6.2 Condition 1.1
    if (curr_time < entry->sym_timer)
    {
        return SYM_LINK;
    }

    // RFC 3626 Section 6.2 Condition 1.2
    if (curr_time < entry->asym_timer)
    {
        return ASYM_LINK;
    }

    // RFC 3626 Section 6.2 Condition 1.3
    return LOST_LINK;
}


// /**
// FUNCTION   :: OlsrLookupLinkEntry
// LAYER      :: APPLICATION
// PURPOSE    :: Looks up link set entry based on local and
//               neighbor interface address
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + remote : Address : neighbor address
// + local : Address : local interface address
// RETURN :: link_entry* : pointer to the link entry
//                         if found, else NULL
// **/

static
link_entry* OlsrLookupLinkEntry(
    Node* node,
    Address remote,
    Address local)
{
    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;
    link_entry* tmp_link_set;

    tmp_link_set = olsr->link_set;

    while (tmp_link_set)
    {
        if ((Address_IsSameAddress(&remote,
                &tmp_link_set->neighbor_iface_addr)) &&
            (Address_IsSameAddress(&local,
                &tmp_link_set->local_iface_addr)))
        {
            return tmp_link_set;
        }

        tmp_link_set = tmp_link_set->next;
    }

    return NULL;
}

// /**
// FUNCTION   :: OlsrPrintLinkSet
// LAYER      :: APPLICATION
// PURPOSE    :: Prints link set neighbors
//               and the local iface address they
//               are attached to
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// RETURN :: void : NULL
// **/

static
void OlsrPrintLinkSet(
    Node* node)
{
    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;
    link_entry* tmp_link_set;

    tmp_link_set = olsr->link_set;

    printf(" Link Set at Node %d\n", node->nodeId);

    char addrString1[MAX_STRING_LENGTH];
    char addrString2[MAX_STRING_LENGTH];

    while (tmp_link_set)
    {
        IO_ConvertIpAddressToString(&tmp_link_set->neighbor_iface_addr,
                                        addrString1);
        IO_ConvertIpAddressToString(&tmp_link_set->local_iface_addr,
                                        addrString2);
        printf(" Neighbor iface addr : %s  Local Iface Addr: %s \n",
            addrString1, addrString2);
        tmp_link_set = tmp_link_set->next;
    }

}


// /**
// FUNCTION   :: OlsrGetNeighborStatus
// LAYER      :: APPLICATION
// PURPOSE    :: Looks up neighbor address in link set and
//               returns the link status
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + address : Address : IP Address of neighbor
// RETURN :: Int32 : status of link
// **/
static
Int32 OlsrGetNeighborStatus(
    Node* node,
    Address address)
{
    Address main_addr;

    unsigned char index;
    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    main_addr = OlsrMidLookupMainAddr(node, address);
    if (Address_IsAnyAddress(&main_addr))
    {
        main_addr = address;
    }

    for (index = 0; index < node->numberInterfaces; index++)
    {
        mid_address* aliases;
        link_entry* link;
        Address ip_addr;
        ip_addr.networkType = NETWORK_IPV4;

        if (NetworkIpGetInterfaceType(node, index) != olsr->ip_version
            && NetworkIpGetInterfaceType(node, index)!= NETWORK_DUAL)
        {
            continue;
        }

        if(olsr->ip_version == NETWORK_IPV6)
        {
            ip_addr.networkType = NETWORK_IPV6;
            Ipv6GetGlobalAggrAddress(
                    node,
                    index,
                    &ip_addr.interfaceAddr.ipv6);
        }
        else if (olsr->ip_version == NETWORK_IPV4)
        {
            ip_addr.networkType = NETWORK_IPV4;
            ip_addr.interfaceAddr.ipv4 =
                            NetworkIpGetInterfaceAddress(node,index);
        }
//#endif

        if ((link = OlsrLookupLinkEntry(node, main_addr, ip_addr))
             != NULL)
        {
            if (OlsrLookupLinkStatus(node, link) == SYM_LINK)
            {
                return SYM_LINK;
            }
        }

        for (aliases = OlsrLookupMidAliases(node, main_addr);
                  aliases != NULL; aliases = aliases->next_alias)
        {
            if ((link = OlsrLookupLinkEntry(node, aliases->alias, ip_addr))
                 != NULL)
            {
                if (OlsrLookupLinkStatus(node,link) == SYM_LINK)
                {
                    return SYM_LINK;
                }
            }
        }
    }

    return 0;
}


// /**
// FUNCTION   :: OlsrUpdateNeighborStatus
// LAYER      :: APPLICATION
// PURPOSE    :: Updates neighbor status in the neighbor table entry depending
//               on the link status passed
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + entry : neighbor_entry * : Pointer to neighbor entry
// + link  : Int32 :  link status
// RETURN :: Int32 : status of neighbor set
// **/
static
Int32 OlsrUpdateNeighborStatus(
    Node* node,
    neighbor_entry* entry,
    Int32 link)
{

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    // Update neighbor entry
    if (link == SYM_LINK)
    {
        // N_status is set to SYM
        if (entry->neighbor_status == NOT_SYM)
        {
            neighbor_2_entry *two_hop_neighbor;

            // Delete posible 2 hop entry on this neighbor
			
			

            if ((two_hop_neighbor = OlsrLookup2HopNeighborTable(node,
                    entry->neighbor_main_addr)) != NULL)
            {
                
				//Peter comment: update the delete list here
				//what is the intention?
				/*
				if (SYMMETRIC_TOPOLOGY_TABLE)
				{

					insert_into_tco_node_addr_set(&olsr->recent_delete_list, entry->neighbor_main_addr.interfaceAddr.ipv4);
				}
				*/
				//DebugBreak();
				
				OlsrDelete2HopNeighborTable(two_hop_neighbor);

				if (SYMMETRIC_TOPOLOGY_TABLE)
				{

					olsr->bNeighborChgCausedRemoveFromHigherHop = TRUE;
					
				}
            }

			if (SYMMETRIC_TOPOLOGY_TABLE)
			{

				rt_entry* rt_tmp = QueryRoutingTableAccordingToNodeId(node, entry->neighbor_main_addr.interfaceAddr.ipv4);

				if (rt_tmp != NULL)
				{

					//Peter Comment: so this cost could be = 2 or > 2 (even 10 for Speed-20-9x9-low- case) 



					/*
					printf("==================NeighborChgCausedRemoveFromHigherHop for node %d with current cost %d \n", node->nodeId, rt_tmp->rt_metric);
					if (rt_tmp->rt_metric > 2)
					{

						printf(" it is larger than 2!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! \n");
					}
					*/

					olsr->bNeighborChgCausedRemoveFromHigherHop = TRUE;
				}
				

			}

            
			//Peter Comment: may need to deal with ###$$$%%%
			//regardless of it has been a 2 hop or not
			//need to partial re-discovery from this neighbor

			if (SYMMETRIC_TOPOLOGY_TABLE)
			{

				insert_into_tco_node_addr_set(&olsr->recent_add_list, entry->neighbor_main_addr.interfaceAddr.ipv4);
			}
			
			olsr->changes_neighborhood = true;
            olsr->changes_topology = true;

			//g_iNeighborChgByOlsrUpdateNeighborStatus++;

			//g_iTopologyChgByOlsrUpdateNeighborStatus++;
        }
        entry->neighbor_status = SYM;
    }
    else
    {
        if (entry->neighbor_status == SYM)
        {

			//Peter Comment: may need to deal with ###$$$%%%
			//this can consider as delete of this route, so delete all its descendants as well
			//delete from route table, or delete by topology table?
			if (SYMMETRIC_TOPOLOGY_TABLE)
			{

				insert_into_tco_node_addr_set(&olsr->recent_delete_list, entry->neighbor_main_addr.interfaceAddr.ipv4);
			}

            olsr->changes_neighborhood = true;
            olsr->changes_topology = true;

	                //g_iNeighborChgByOlsrUpdateNeighborStatus++;

			//g_iTopologyChgByOlsrUpdateNeighborStatus++;
        }
        // else N_status is set to NOT_SYM

        if(DEBUG)
        {
            printf(" Node %d : Setting status of neighbor as NOT SYM\n",
                node->nodeId);
        }

        entry->neighbor_status = NOT_SYM;
        // remove neighbor from routing list
    }

    return entry->neighbor_status;
}



// /**
// FUNCTION   :: OlsrAddNewLinkEntry
// LAYER      :: APPLICATION
// PURPOSE    :: Searches for an entry in link set
//               If not found, adds a new link entry
//               to the link set
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + local : Address : local interface IP Address
// + remote : Address : Neighbor interface IP Address
// + remote_main : Address : Neighbor Main IP Address
// + vtime : Float32 : validity time of entry
// + htime : Float32 : hello interval of the neighbor node
// RETURN :: link_entry* : Pointer to the found/new added entry
// **/

static
link_entry* OlsrAddNewLinkEntry(
    Node* node,
    Address local,
    Address remote,
    Address remote_main,
    Float32 vtime)
{
    link_entry *tmp_link_set, *new_link;
    neighbor_entry *neighbor;

   if (DEBUG)
   {
       printf(" In adding new entry function\n");
   }

   RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

   if (DEBUG)
   {
       if(olsr->link_set == NULL)
       {
           printf(" Node %d: Link set is NULL\n", node->nodeId);
       }
   }

   tmp_link_set = olsr->link_set;

   while (tmp_link_set)
   {
       if ((Address_IsSameAddress(&remote,
                &tmp_link_set->neighbor_iface_addr)) &&
           (Address_IsSameAddress(&local,
                &tmp_link_set->local_iface_addr)))
       {
           return tmp_link_set;
       }

       tmp_link_set = tmp_link_set->next;
    }

   if (DEBUG)
   {
       printf(" Node %d: Adding New entry in the link set\n",node->nodeId);
   }

   // RFC 3626 Section 7.1.1 Condition 1

   // if there exists no link tuple with
   // L_neighbor_iface_addr == Source Address

   // a new tuple is created with..

   new_link = (link_entry *)MEM_malloc(sizeof(link_entry));

   memset(new_link, 0 , sizeof(link_entry));

   // L_local_iface_addr = Address of the interface
   // which received the HELLO message

   new_link->local_iface_addr = local;

   // L_neighbor_iface_addr = Source Address
   new_link->neighbor_iface_addr = remote;

   // L_SYM_time = current time - 1 (expired)

   new_link->sym_timer = getSimTime(node) - 1;

   // L_time = current time + validity time
   new_link->timer = getSimTime(node) + (clocktype) (vtime * SECOND);

   new_link->prev_status = ASYM_LINK;

   // Add to queue
   new_link->next = olsr->link_set;
   olsr->link_set = new_link;

   // Create the neighbor entry

   // Neighbor MUST exist!
   neighbor = OlsrLookupNeighborTable(node, remote_main);
   if (!(neighbor))
   {
       neighbor = (neighbor_entry *) MEM_malloc(sizeof(neighbor_entry));
       memset(neighbor, 0, sizeof(neighbor_entry));
       neighbor->neighbor_main_addr = remote_main;
       neighbor->neighbor_willingness = WILL_NEVER;
       neighbor->neighbor_status = NOT_SYM;
       neighbor->neighbor_linkcount = 0;
       neighbor->neighbor_is_mpr = FALSE;
       neighbor->neighbor_was_mpr = FALSE;
       neighbor->neighbor_2_list = NULL;
       neighbor->neighbor_2_nocov = 0;
       OlsrInsertNeighborTable(node, neighbor);
   }

   // Copy the main address - make sure this is done every time
   // as neighbors might change main address

   neighbor->neighbor_main_addr = remote_main;

   neighbor->neighbor_linkcount++;

   new_link->neighbor = neighbor;

   if (!Address_IsSameAddress(&remote, &remote_main))
   {
       // Add MID alias if not already registered
       // This is kind of sketchy... and not specified
       // in the RFC. We can only guess a vtime.
       // We'll go for one that is hopefully long
       // enough in most cases. 20 seconds

       // Need to check if alias is already present in table..this is
       // not done in olsrd

       Address main_addr = OlsrMidLookupMainAddr(node, remote);

       if (Address_IsAnyAddress(&main_addr))
       {
           OlsrInsertMidAlias(node, remote_main, remote, 20.0);
       }
    }

  return new_link;
}


// /**
// FUNCTION   :: OlsrCheckLinktoNeighbor
// LAYER      :: APPLICATION
// PURPOSE    :: Lookup status of the link corresponding to the neighbor
//               address
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + int_addr: Address: interface address to look up
// RETURN :: Int32 :  link status
// **/

static
Int32 OlsrCheckLinktoNeighbor(
    Node* node,
    Address int_addr)
{
    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;
    link_entry*  link_set=olsr->link_set;
    link_entry*     tmp_link_set;

    tmp_link_set = link_set;

    while (tmp_link_set)
    {
        if (Address_IsSameAddress(&int_addr,
                &tmp_link_set->neighbor_iface_addr))
        {
            return OlsrLookupLinkStatus(node, tmp_link_set);
        }
        tmp_link_set = tmp_link_set->next;
    }
    return UNSPEC_LINK;
}

// /**
// FUNCTION   :: OlsrGetLinktoNeighbor
// LAYER      :: APPLICATION
// PURPOSE    ::  Function returns a link where neighbor interface
//                address matches remote address
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + remote: Address: Neighbor interface IP Address
// RETURN :: link_entry* : Pointer to the found entry
// **/

static
link_entry* OlsrGetLinktoNeighbor(
    Node* node,
    Address remote)
{
    link_entry* walker;
    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    link_entry* link_set = olsr->link_set;

    for (walker = link_set; walker != NULL; walker = walker->next)
    {
        // Perfect match..
        if (Address_IsSameAddress(&walker->neighbor_iface_addr, &remote))
        {
            return walker;
        }
    }

    return NULL;
}


// /**
// FUNCTION   :: OlsrGetBestLinktoNeighbor
// LAYER      :: APPLICATION
// PURPOSE    ::  Function returns a link where neighbor interface
//                address matches alias address/remote address
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + remote: Address: Neighbor interface IP Address
// RETURN :: link_entry* : Pointer to the found entry
// **/

static
link_entry* OlsrGetBestLinktoNeighbor(
    Node* node,
    Address remote)
{
    Address main_addr;
    link_entry* walker;
    link_entry* good_link;

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    link_entry* link_set = olsr->link_set;

    main_addr = OlsrMidLookupMainAddr(node, remote);

    if (Address_IsAnyAddress(&main_addr))
    {
        main_addr = remote;
    }

    good_link = NULL;

    for (walker = link_set; walker != NULL; walker = walker->next)
    {
        if (!Address_IsSameAddress(&walker->neighbor->neighbor_main_addr,
                &main_addr))
        {
            continue;
        }

        // Perfect match..if the neighbor iface address for this link
        // matches the address we are looking up

        if (Address_IsSameAddress(&walker->neighbor_iface_addr, &remote))
        {
            return walker;
        }
        else
        {
            // Didn't find a match, we need to set a backup to send in
            // case  a perfect match doesn't occur

            good_link = walker;
        }

    }

    if (Address_IsSameAddress(&remote, &main_addr))
    {
        // Return any associated link tuple if main addr
        // and no perfecr match found

        return good_link;
    }
    else
    {
        // if remote is not the main address, we still need to send any
        // link if present that can get to the main address node

        if (good_link)
        {
            return good_link;
        }
        else
        {
            return NULL;
        }
    }
}


// /**
// FUNCTION   :: OlsrCheckLinkStatus
// LAYER      :: APPLICATION
// PURPOSE    :: Checks the link status to a neighbor by
//               looking in a received HELLO message.
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + message:  hl_message* : Pointer to the hello message
// + interfaceIndex: Int32: interface on which hello was received
// RETURN :: unsigned char : Link status in the hello packet
// **/
static
unsigned char OlsrCheckLinkStatus(
    Node* node,
    hl_message* message,
    Int32 interfaceIndex)
{
    hello_neighbor* neighbors;
    neighbors = message->neighbors;
    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;
    while (neighbors!=NULL)
    {
        Address ip_addr;


        if(olsr->ip_version == NETWORK_IPV6)
        {
            ip_addr.networkType = NETWORK_IPV6;
            Ipv6GetGlobalAggrAddress(
                    node,
                    interfaceIndex,
                    &ip_addr.interfaceAddr.ipv6);
        }
        else if (olsr->ip_version == NETWORK_IPV4)
        {
            ip_addr.networkType = NETWORK_IPV4;
            ip_addr.interfaceAddr.ipv4 =
                            NetworkIpGetInterfaceAddress(node,interfaceIndex);
        }
//#endif

        if (Address_IsSameAddress(&neighbors->address, &ip_addr))
        {
            return neighbors->link;
        }

        neighbors = neighbors->next;
    }

    if (DEBUG)
    {
        printf(" Node %d: Returning unspec link as link status \n",
            node->nodeId);
    }

    return UNSPEC_LINK;
}


// /**
// FUNCTION   :: OlsrUpdateLinkEntry
// LAYER      :: APPLICATION
// PURPOSE    :: Updates a link entry, is main entrypoint in link-sensing
//               Function is called from Hello processing fn
//               Updates an existing entry or creates a new one
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + local: Address: local interface IP Address
// + remote: Address: Neighbor interface IP Address
// + message : hl_message* : Pointer to the hello message
// + interfaceIndex: Int32: interface on which message is received
// RETURN :: link_entry* : Pointer to the updated/new added entry
// **/

static
link_entry* OlsrUpdateLinkEntry(
    Node* node,
    Address local,
    Address remote,
    hl_message* message,
    Int32 interfaceIndex)
{
    if (DEBUG)
    {
        printf (" Node %d : updating link entry for neighbor\n",
            node->nodeId);
    }

    link_entry* entry;
    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    // Add if not registered
    entry = OlsrAddNewLinkEntry(node,
                local, remote, message->source_addr,
                message->vtime);

    // RFC 3626 Section 7.1.1 Condition 2

   // Update ASYM_time

   // L_ASYM_time = current time + validity time
   entry->asym_timer = getSimTime(node)
                       + (clocktype)(message->vtime * SECOND);

   entry->prev_status = OlsrCheckLinkStatus(node, message,interfaceIndex);

   switch (entry->prev_status)
   {
       case (LOST_LINK):
       {
            if (DEBUG)
            {
                printf(" Node %d : Prev status was lost link\n",
                    node->nodeId);
            }

            // L_SYM_time = current time - 1 (i.e., expired)

            entry->sym_timer = getSimTime(node) - 1;

            break;
        }
      case(SYM_LINK):
      case(ASYM_LINK):
      {
            if (DEBUG)
            {
                printf(" Node %d : Prev status was sym/asym link\n",
                    node->nodeId);
            }
            // L_SYM_time = current time + validity time

            entry->sym_timer = getSimTime(node)
                               + (clocktype) (message->vtime * SECOND);

            // L_time = L_SYM_time + olsr->neighb_hold_time

            entry->timer = getSimTime(node) + olsr->neighb_hold_time;

            break;
      }

      default:
      {
            if (DEBUG)
            {
                printf(" Node %d : Prev status is undefined\n",node->nodeId);
            }
            break;
      }

  }

  // L_time = max(L_time, L_ASYM_time)
  if (entry->timer < entry->asym_timer)
  {
    entry->timer = entry->asym_timer;
  }

  // Update neighbor
  OlsrUpdateNeighborStatus(node,
    entry->neighbor, OlsrGetNeighborStatus(node, remote));

  return entry;
}


// /**
// FUNCTION   :: OlsrReplaceNeighborLinkEntry
// LAYER      :: APPLICATION
// PURPOSE    :: Searches for a neighbor entry in link set
//               If  found, replaces that entry
//               with a new entry
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + old_neighbor: neighbor_entry* : old neighbor entry
// + new_neighbor: neighbor_entry* : new neighbor entry
// RETURN :: Int32 : Number of entries replaced
// **/
static
Int32 OlsrReplaceNeighborLinkEntry(
    Node* node,
    neighbor_entry* old_neighbor,
    neighbor_entry* new_neighbor)
{
    link_entry* tmp_link_set;
    Int32 retval = 0;

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    if (olsr->link_set == NULL)
    {
        return retval;
    }

    tmp_link_set = olsr->link_set;

    while (tmp_link_set)
    {

        if (tmp_link_set->neighbor == old_neighbor)
        {
            tmp_link_set->neighbor = new_neighbor;
            retval++;
        }
        tmp_link_set = tmp_link_set->next;
    }

    return retval;
}


// /**
// FUNCTION   :: OlsrTimeoutLinkEntry
// LAYER      :: APPLICATION
// PURPOSE    :: Removes expired link entries in link set
//               Also removes unreferenced neighbors from neighbor table
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// RETURN :: void : NULL
// **/

static
void OlsrTimeoutLinkEntry(
    Node* node)
{
    if (DEBUG)
    {
        printf("Node %d: Timing out Link set\n",node->nodeId);
    }

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;
    link_entry* tmp_link_set;
    link_entry* last_link_entry;

    if (olsr->link_set == NULL)
    {
        return;
    }

    tmp_link_set = olsr->link_set;
    last_link_entry = NULL;

    while (tmp_link_set)
    {
        if (getSimTime(node) > tmp_link_set->timer)
        {
            if (last_link_entry != NULL)
            {
                last_link_entry->next = tmp_link_set->next;

                // RFC 3626 Section 8.1 Removal Condition

                // Delete neighbor entry
                if (tmp_link_set->neighbor->neighbor_linkcount == 1)
                {

                    // Delete MPR selector entry corresponding to this
                    // neighbor?
                    // This is missing from olsrd but present in Section 8.5

                        mpr_selector_entry* selector_entry =
                                OlsrLookupMprSelectorTable(node,
                                tmp_link_set->neighbor->neighbor_main_addr);


                    if (selector_entry != NULL)
                    {
                        mpr_selector_entry* mprs_tmp = selector_entry;

                        selector_entry = selector_entry->mpr_selector_forw;
                        OlsrDeleteMprSelectorTable(mprs_tmp);
                        olsr->mprstable.ansn++;
                    }
                    OlsrDeleteNeighborTable(tmp_link_set->neighbor);
                }
                else
                {
                    tmp_link_set->neighbor->neighbor_linkcount --;
                }

                          g_iNeighborChgByOlsrTimeoutLinkEntry++;

				////Peter Comment: skip this one, just let it do re-calculation
                olsr->changes_neighborhood = TRUE;
                MEM_free(tmp_link_set);
                tmp_link_set = last_link_entry;
            }
            else
            {
                olsr->link_set = tmp_link_set->next; // CHANGED

                // Delete neighbor entry
                if (tmp_link_set->neighbor->neighbor_linkcount == 1)
                {

                    // Delete MPR selector entry corresponding to this
                    // neighbor?

                    // This is missing from olsrd but present in Section 8.5
                    mpr_selector_entry* selector_entry =
                        OlsrLookupMprSelectorTable(node,
                            tmp_link_set->neighbor->neighbor_main_addr);

                    if (selector_entry != NULL)
                    {
                        mpr_selector_entry* mprs_tmp = selector_entry;

                        selector_entry = selector_entry->mpr_selector_forw;
                        OlsrDeleteMprSelectorTable(mprs_tmp);
                        olsr->mprstable.ansn++;
                    }
                    OlsrDeleteNeighborTable(tmp_link_set->neighbor);
                }
                else
                {
                    tmp_link_set->neighbor->neighbor_linkcount--;
                }


                     g_iNeighborChgByOlsrTimeoutLinkEntry++;

				 //Peter Comment: skip this one, just let it do re-calculation
                olsr->changes_neighborhood = TRUE;
                MEM_free(tmp_link_set);
                tmp_link_set = olsr->link_set;
                continue;
            }

        }
        else if ((tmp_link_set->prev_status == SYM_LINK) &&
                 (getSimTime(node)>tmp_link_set->sym_timer))
        {
            tmp_link_set->prev_status = (unsigned char)OlsrLookupLinkStatus(
                                                          node,tmp_link_set);
            OlsrUpdateNeighborStatus(node, tmp_link_set->neighbor,
                    OlsrGetNeighborStatus(node,
                        tmp_link_set->neighbor_iface_addr));

                       g_iNeighborChgByOlsrTimeoutLinkEntry++;

		   //Peter Comment: skip this one, just let it do re-calculation
            olsr->changes_neighborhood = TRUE;
        }
        last_link_entry = tmp_link_set;
        tmp_link_set = tmp_link_set->next;
    }

    return;
}


/***************************************************************************
 *                    Definition of Duplicate Table
 ***************************************************************************/

// /**
// FUNCTION   :: OlsrDeleteDuplicateTable
// LAYER      :: APPLICATION
// PURPOSE    :: Deletes an entry from duplicate table
// PARAMETERS ::
// + dup_entry : duplicate_entry* : Pointer to duplicate entry
// RETURN :: void : NULL
// **/

static
void OlsrDeleteDuplicateTable(
    duplicate_entry* dup_entry)
{
    duplicate_ifaces *tmp_iface, *del_iface;
    tmp_iface = dup_entry->dup_ifaces;

    //Free Interfaces
    while (tmp_iface)
    {
        del_iface = tmp_iface;
        tmp_iface = tmp_iface->duplicate_iface_next;
        MEM_free(del_iface);
    }

    OlsrRemoveList((olsr_qelem *)dup_entry);
    MEM_free((void *)dup_entry);
}

// /**
// FUNCTION   :: OlsrInsertDuplicateTable
// LAYER      :: APPLICATION
// PURPOSE    :: Inserts an entry in duplicate table
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + originator : Address:  address of node to be inserted
// + packet_seq_number: UInt16: sequence number to be inserted
// RETURN :: duplicate_entry * : Pointer to entry inserted
// **/

static
duplicate_entry* OlsrInsertDuplicateTable(
    Node* node,
    Address originator,
    UInt16 packet_seq_number)
{
    UInt32 hash;
    duplicatehash* dup_hash;
    duplicate_entry* dup_message;

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    dup_message = (duplicate_entry *) MEM_malloc(sizeof(duplicate_entry));
    memset(dup_message, 0, sizeof(duplicate_entry));

    // create a duplicate tuple
    dup_message->duplicate_seq = packet_seq_number;
    dup_message->duplicate_addr = originator;
    dup_message->duplicate_timer = getSimTime(node) +
            olsr->dup_hold_time;

    // New RFC version variables
    dup_message->duplicate_retransmitted = 0;
    dup_message->dup_ifaces = NULL;

    OlsrHashing(dup_message->duplicate_addr, &hash);
    dup_message->duplicate_hash = hash;
    dup_hash = &olsr->duplicatetable[hash % HASHMASK];

    // insert in the list
    OlsrInsertList((olsr_qelem *)dup_message, (olsr_qelem *)dup_hash);
    return dup_message;
}

// /**
// FUNCTION   :: OlsrLookupDuplicateTableProc
// LAYER      :: APPLICATION
// PURPOSE    :: Search in duplicate table  if  originator and seq no are
//               processed
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + originator : Address : originator of the message
// + packet_seq_number : UInt16 : sequence number of message
// RETURN :: duplicate_entry * : Pointer to found entry else NULL
// **/

static
duplicate_entry* OlsrLookupDuplicateTableProc(
    Node *node,
    Address originator,
    UInt16 packet_seq_number)
{
    duplicate_entry* dup_message;
    duplicatehash* dup_hash;
    UInt32 hash;

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    OlsrHashing(originator, &hash);

    dup_hash = &olsr->duplicatetable[hash % HASHMASK];

    // search in the duplicate table
    for (dup_message = dup_hash->duplicate_forw;
        dup_message != (duplicate_entry *) dup_hash;
        dup_message = dup_message->duplicate_forw)
    {
        if (dup_message->duplicate_hash != hash)
        {
            continue;
        }

        // RFC 3626 Section 3.4 Condition 3

        // if originator address in table and sequence number matches
        if (Address_IsSameAddress(&dup_message->duplicate_addr, &originator)
            && (dup_message->duplicate_seq == packet_seq_number))
        {
            if (DEBUG)
            {
                printf("message is in the duplicate table seqNo. is %d\n",
                        dup_message->duplicate_seq);
            }

            // entry found
            return (dup_message);
        }
    }
    // entry not found
    return (NULL);
}


// /**
// FUNCTION   :: OlsrLookupDuplicateTableFwd
// LAYER      :: APPLICATION
// PURPOSE    :: Search in duplicate table  if originator and seq no exist
//               in fwd list
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + originator: Address: originator node
// + packet_seq_number : UInt16 : sequence no
// RETURN :: Int32 : 0 if already fwded, 1 if not
// **/

static
Int32 OlsrLookupDuplicateTableFwd(
    Node *node,
    Address originator,
    UInt16 packet_seq_number,
    Address interfaceAddress)
{
    duplicate_entry* dup_message;
    duplicatehash* dup_hash;
    UInt32 hash;

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    OlsrHashing(originator, &hash);

    dup_hash = &olsr->duplicatetable[hash % HASHMASK];
    // search in the duplicate table
    for (dup_message = dup_hash->duplicate_forw;
        dup_message != (duplicate_entry *) dup_hash;
        dup_message = dup_message->duplicate_forw)
    {
        if (dup_message->duplicate_hash != hash)
        {
            continue;
        }

        // RFC 3626 Section 3.4 Condition  4, Section 3.4.1

        // if originator address in table and sequence number matches
        if (Address_IsSameAddress(&dup_message->duplicate_addr, &originator)
            && (dup_message->duplicate_seq == packet_seq_number))
        {
            // Check retransmitted
            if (dup_message->duplicate_retransmitted)
            {
                return 0;
            }

            duplicate_ifaces* dup_iface;
            dup_iface = dup_message->dup_ifaces;
            while (dup_iface)
            {
                if (Address_IsSameAddress(&dup_iface->interfaceAddress,
                        &interfaceAddress))
                {
                    return 0;
                }
                dup_iface = dup_iface->duplicate_iface_next;
            }
        }
    }
    return 1;
}


// /**
// FUNCTION   :: OlsrReleaseDuplicateTable
// LAYER      :: APPLICATION
// PURPOSE    :: Release all the entries from duplicate table
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// RETURN :: void : NULL
// **/

static
void OlsrReleaseDuplicateTable(
    Node* node)
{
    Int32 index;
    duplicatehash* dup_hash;
    duplicate_entry* dup_message;
    duplicate_entry* dup_message_tmp;

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    // get each entry from the table and delete it
    for (index = 0; index < HASHSIZE; index++)
    {
        dup_hash = &olsr->duplicatetable[index];
        dup_message = dup_hash->duplicate_forw;
        while (dup_message != (duplicate_entry *) dup_hash)
        {
            dup_message_tmp = dup_message;
            dup_message = dup_message->duplicate_forw;
            OlsrDeleteDuplicateTable(dup_message_tmp);
        }
    }
}


// /**
// FUNCTION   :: OlsrTimeoutDuplicateTable
// LAYER      :: APPLICATION
// PURPOSE    :: This function will be called when olsr->dup_hold_time
//               R times out. Check the entries with the current time
//               and delete if hold timer is less than current time.
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// RETURN :: void : NULL
// **/

static
void OlsrTimeoutDuplicateTable(
     Node* node)
{
    Int32 index;
    duplicatehash* dup_hash;
    duplicate_entry* dup_message;
    duplicate_entry* dup_message_tmp;

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    for (index = 0; index < HASHSIZE; index++)
    {
        dup_hash = &olsr->duplicatetable[index];
        dup_message = dup_hash->duplicate_forw;
        while (dup_message != (duplicate_entry *) dup_hash)
        {
            // if current time exceeds duplicate hold time then delete it
            if (getSimTime(node) >= dup_message->duplicate_timer)
            {
                dup_message_tmp = dup_message;
                dup_message = dup_message->duplicate_forw;
                OlsrDeleteDuplicateTable(dup_message_tmp);
            }
            else
            {
                dup_message = dup_message->duplicate_forw;
            }
        }
    }
}

// /**
// FUNCTION   :: OlsrUpdateDuplicateEntry
// LAYER      :: APPLICATION
// PURPOSE    :: Searches for an entry in duplicate table
//               if not found, adds a new entry
//               Then updates the status of the found/newly added entry
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + originator : Address : originator of the msg
// + packet_seq_number : UInt16 : sequence no of mesg
// + interfaceAddress : Address: Address of the interface
// RETURN :: Int32 : 1 to indicate successful updation
// **/

static
Int32 OlsrUpdateDuplicateEntry(
    Node *node,
    Address originator,
    UInt16 packet_seq_number,
    Address interfaceAddress)
{
    duplicate_entry* dup_message;
    duplicatehash* dup_hash;
    UInt32 hash;
    duplicate_ifaces* new_iface;

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    OlsrHashing(originator, &hash);

    dup_hash = &olsr->duplicatetable[hash % HASHMASK];
    // search in the duplicate table
    for (dup_message = dup_hash->duplicate_forw;
        dup_message != (duplicate_entry *) dup_hash;
        dup_message = dup_message->duplicate_forw)
    {

        if (dup_message->duplicate_hash != hash)
        {
            continue;
        }

        // if originator address in table and sequence number matches
        if (Address_IsSameAddress(&dup_message->duplicate_addr, &originator)
            && (dup_message->duplicate_seq == packet_seq_number))
        {
            break;
        }
    }

    if(dup_message == (duplicate_entry *)dup_hash)
    {
        // Did not find entry - create it
        dup_message = OlsrInsertDuplicateTable(node,
                          originator, packet_seq_number);
    }

    // RFC 3626 Section 3.4.1  Condition 5

    // 0 for now
    dup_message->duplicate_retransmitted = 0;
    new_iface = (duplicate_ifaces *)MEM_malloc(sizeof(duplicate_ifaces));
    memset(new_iface, 0, sizeof(duplicate_ifaces));
    new_iface->interfaceAddress = interfaceAddress;
    new_iface->duplicate_iface_next = dup_message->dup_ifaces;
    dup_message->dup_ifaces = new_iface;

    // Set timer
    dup_message->duplicate_timer = getSimTime(node) +
                                       olsr->dup_hold_time;

    return 1;
}


// /**
// FUNCTION   :: OlsrSetDuplicateForward
// LAYER      :: APPLICATION
// PURPOSE    :: Searches for an entry in table and sets the retransmitted
//               flag for the message entry
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + originator : Address : originator of message
// + packet_seq_number: UInt16: sequence number of the message
// RETURN :: Int32 : 0 if not found, 1 if found and flag set
//
// **/

static
Int32 OlsrSetDuplicateForward(
    Node *node,
    Address originator,
    UInt16 packet_seq_number)
{
    duplicate_entry* dup_message;
    duplicatehash* dup_hash;
    UInt32 hash;

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    OlsrHashing(originator, &hash);

    dup_hash = &olsr->duplicatetable[hash % HASHMASK];
    // search in the duplicate table
    for (dup_message = dup_hash->duplicate_forw;
        dup_message != (duplicate_entry *) dup_hash;
        dup_message = dup_message->duplicate_forw)
    {
        if (dup_message->duplicate_hash != hash)
        {
            continue;
        }

        // if originator address in table and sequence number matches
        if (Address_IsSameAddress(&dup_message->duplicate_addr, &originator)
            && (dup_message->duplicate_seq == packet_seq_number))
        {
            break;
        }
    }

    if(dup_message == (duplicate_entry *)dup_hash)
    {
        return 0;
    }

    // RFC 3626 Section 3.4.1 Condition 5

    // Set forwarded
    dup_message->duplicate_retransmitted = 1;

    // Set timer
    dup_message->duplicate_timer = getSimTime(node)
                                       + olsr->dup_hold_time;

    return 1;
}

// /**
// FUNCTION   :: OlsrPrintDuplicateTable
// LAYER      :: APPLICATION
// PURPOSE    :: Print contents of Duplicate table
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// RETURN :: void : NULL
// **/
static
void OlsrPrintDuplicateTable(
    Node* node)
{
    Int32 index;
    duplicatehash* dup_hash;
    duplicate_entry* dup_message;

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    printf("Duplicate Table\n");
    printf("Hash       Address         Duplicate Seq No.\n");

    for (index = 0; index < HASHSIZE; index++)
    {
        dup_hash = &olsr->duplicatetable[index];

        for (dup_message = dup_hash->duplicate_forw;
            dup_message != (duplicate_entry *) dup_hash;
            dup_message = dup_message->duplicate_forw)
        {
            char addrString[MAX_STRING_LENGTH];

            IO_ConvertIpAddressToString(&dup_message->duplicate_addr,
                                        addrString);
            printf("%-10d %-15s %d\n",
                dup_message->duplicate_hash,
                addrString, dup_message->duplicate_seq);
        }
    }
}

/***************************************************************************
 *                 Neighbor Table related functions                        *
 ***************************************************************************/

// /**
// FUNCTION   :: OlsrDeleteNeighbor2Pointer
// LAYER      :: APPLICATION
// PURPOSE    :: Deletes current address from the 2 hop neighbor list of this
//               neighbor entry
// PARAMETERS ::
// + neighbor : neighbor_entry* : Pointer to neighbor entry
// + address : Address : Address to be deleted from two hop neighbor list
// RETURN :: void : NULL
// **/

void OlsrDeleteNeighbor2Pointer(
    neighbor_entry* neighbor,
    Address address)
{
    neighbor_2_list_entry* neighbor_two_list;
    neighbor_2_list_entry* neighbor_two_list_tmp;

    ERROR_Assert(neighbor, "Invalid neighbor entry");

    // get 2 hop list for current enighbor entry
    neighbor_two_list = neighbor->neighbor_2_list;

    if (Address_IsSameAddress(
                    &neighbor_two_list->neighbor_2->neighbor_2_addr,
                    &address))
    {
        // 2 hop matches going to delete it
        neighbor->neighbor_2_list = neighbor_two_list->neighbor_2_next;
        MEM_free(neighbor_two_list);
        return;
    }

    neighbor_two_list_tmp = neighbor_two_list;
    neighbor_two_list = neighbor_two_list->neighbor_2_next;

    while (neighbor_two_list != NULL)
    {
        if (Address_IsSameAddress(
                            &neighbor_two_list->neighbor_2->neighbor_2_addr,
                            &address))
        {
            // 2 hop matches going to delete it
            neighbor_two_list_tmp->neighbor_2_next =
                                neighbor_two_list->neighbor_2_next;
            MEM_free(neighbor_two_list);
            return;
        }
        else
        {
            // searches for the next in the 2 hop neighbor table
            neighbor_two_list_tmp = neighbor_two_list;
            neighbor_two_list = neighbor_two_list->neighbor_2_next;
        }
    }
}

// /**
// FUNCTION   :: OlsrLookupMyNeighbors
// LAYER      :: APPLICATION
// PURPOSE    :: Searches this neighbor address in the current neighbor entry
//               neighbor entry
// PARAMETERS ::
// + neighbor : neighbor_entry* : Pointer to neighbor entry
// + neighbor_main_address : Address : Address to be searched
// RETURN :: neighbor_2_list_entry * : corresponding two hop neighbor list
//                                     entry
// **/

static
neighbor_2_list_entry* OlsrLookupMyNeighbors(
    neighbor_entry* neighbor,
    Address neighbor_main_address)
{
    neighbor_2_list_entry* neighbor_two_list;

    ERROR_Assert(neighbor, "Invalid neighbor entry");

    neighbor_two_list = neighbor->neighbor_2_list;

    while (neighbor_two_list != NULL)
    {
        if (Address_IsSameAddress(
            &neighbor_two_list->neighbor_2->neighbor_2_addr,
            &neighbor_main_address))
        {
            // address matches return 2 hop neighbor list
            return(neighbor_two_list);
        }
        neighbor_two_list = neighbor_two_list->neighbor_2_next;
    }
    return NULL;
}


// /**
// FUNCTION   :: OlsrDeleteNeighborPointer
// LAYER      :: APPLICATION
// PURPOSE    :: This procedure deletes the pointer to this addr from
//               the list contained in the two hop neighbor entry
// PARAMETERS ::
// + two_hop_entry  : neighbor_2_entry * : Pointer to two hop neighbor list
// + address : Address: Address to be removed from 2 hop list
// RETURN :: void : NULL
// **/

static
void OlsrDeleteNeighborPointer(
    neighbor_2_entry* two_hop_entry,
    Address address)
{
    neighbor_list_entry* one_hop_list;
    neighbor_list_entry* one_hop_list_tmp;

    ERROR_Assert(two_hop_entry, "Invalid two hop neighbor entry");

    // get one hop list from the 2 hop entry
    one_hop_list = two_hop_entry->neighbor_2_nblist;

    if (Address_IsSameAddress(
            &one_hop_list->neighbor->neighbor_main_addr, &address))
    {
        two_hop_entry->neighbor_2_nblist = one_hop_list->neighbor_next;
        MEM_free(one_hop_list);
        return;
    }

    one_hop_list_tmp = one_hop_list;
    one_hop_list = one_hop_list->neighbor_next;

    while (one_hop_list)
    {
        if (Address_IsSameAddress(
                &one_hop_list->neighbor->neighbor_main_addr, &address))
        {
            one_hop_list_tmp->neighbor_next = one_hop_list->neighbor_next;
            MEM_free(one_hop_list);
            return;
        }
        else
        {
            one_hop_list_tmp = one_hop_list;
            one_hop_list = one_hop_list->neighbor_next;
        }
    }
}

// /**
// FUNCTION   :: OlsrDeleteNeighborTable
// LAYER      :: APPLICATION
// PURPOSE    :: Deletes current neighbor entry from the neighbor table
// PARAMETERS ::
// + neighbor : neighbor_entry* : Pointer to entry to be deleted
// RETURN :: void : NULL
// **/

void OlsrDeleteNeighborTable(
    neighbor_entry* neighbor)
{
    neighbor_2_list_entry* two_hop_list;
    neighbor_2_entry*   two_hop_entry;

    ERROR_Assert(neighbor, "Invalid neighbor entry");

    // delete 2 hop neighbor table for this neighbor
    two_hop_list = neighbor->neighbor_2_list;

    while (two_hop_list != NULL)
    {
        two_hop_entry = two_hop_list->neighbor_2;
        two_hop_entry->neighbor_2_pointer--;

        OlsrDeleteNeighborPointer(two_hop_entry,
            neighbor->neighbor_main_addr);

        if (two_hop_entry->neighbor_2_pointer < 1)
        {
            // means this two hop entry is no more pointed, not reachable
            OlsrRemoveList((olsr_qelem *) two_hop_entry);
            MEM_free((void *) two_hop_entry);
        }

        neighbor->neighbor_2_list = two_hop_list->neighbor_2_next;
        MEM_free(two_hop_list);
        two_hop_list = neighbor->neighbor_2_list;
    }

    // deletes neighbor
    OlsrRemoveList((olsr_qelem *) neighbor);
    MEM_free((void *)neighbor);
}


// /**
// FUNCTION   :: OlsrInsertNeighborTable
// LAYER      :: APPLICATION
// PURPOSE    :: Inserts neighbor entry in the neighbor table
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + neighbor: neighbor_entry * : entry to be inserted
// RETURN :: void : NULL
// **/
void OlsrInsertNeighborTable(
    Node* node,
    neighbor_entry* neighbor)
{
    UInt32 hash;
    neighborhash_type* hash_neighbor;

    RoutingOlsr* olsr = (RoutingOlsr*) node->appData.olsr;

    ERROR_Assert(neighbor, "Invalid neighbor entry");

    OlsrHashing(neighbor->neighbor_main_addr, &hash);
    neighbor->neighbor_hash = hash;

    hash_neighbor = &olsr->neighbortable.neighborhash[hash % HASHMASK];

        //Peter added for support...


	double dDistance = 0.0;
	double dRWON = ComputeRouterDegreeWRTOriginNode(node, neighbor->neighbor_main_addr.interfaceAddr.ipv4, &dDistance);
	dRWON = SimulateLocalDirectionOfAoA(node, dRWON);
	
	neighbor->neighbor_infos.dDegreeWRTNode = dRWON;
	neighbor->neighbor_infos.dDistanceWRTNode = dDistance;



	//hash_neighbor = &olsr->neighbortable.neighborhash[index];

	if (g_iKeepOrder == 1)
	{

		neighbor_entry* tmp_neighbor = hash_neighbor->neighbor_forw;
		neighbor_entry* tmp_neighbor_last = (neighbor_entry *) hash_neighbor;

		if (tmp_neighbor != (neighbor_entry *) hash_neighbor)
		{
			
			while (tmp_neighbor != (neighbor_entry *) hash_neighbor)
			{
				if (tmp_neighbor->neighbor_hash > neighbor->neighbor_hash)
				{
					
					//OlsrInsertList((olsr_qelem *)neighbor, (olsr_qelem *)tmp_neighbor_last);
					

					
					break;
				}
				else
				{
					tmp_neighbor_last = tmp_neighbor;
					
					tmp_neighbor = tmp_neighbor->neighbor_forw;
				}
			}
			

			neighbor->neighbor_back = tmp_neighbor_last;
			neighbor->neighbor_forw = tmp_neighbor;

			tmp_neighbor_last->neighbor_forw = neighbor;

			tmp_neighbor->neighbor_back = neighbor;
		}
		else
		{
			OlsrInsertList((olsr_qelem *)neighbor, (olsr_qelem *)hash_neighbor);
		}

		
	}
	else
	{

		OlsrInsertList((olsr_qelem *)neighbor, (olsr_qelem *)hash_neighbor);
	}


}

// /**
// FUNCTION   :: OlsrLookupNeighborTable
// LAYER      :: APPLICATION
// PURPOSE    :: Searches neighbor table for this address
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + dst : Address: Address to look for
// RETURN :: neighbor_entry * : if found, pointer to entry
//                              else NULL
// **/
neighbor_entry* OlsrLookupNeighborTable(
    Node* node,
    Address dst)
{
    neighbor_entry* neighbor;
    neighborhash_type* hash_neighbor;
    UInt32 hash;
    Address tmp_addr = OlsrMidLookupMainAddr(node, dst);

    if(!Address_IsAnyAddress(&tmp_addr))
    {
        dst = tmp_addr;
    }

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    OlsrHashing(dst, &hash);
    hash_neighbor = &olsr->neighbortable.neighborhash[hash % HASHMASK];

    for (neighbor = hash_neighbor->neighbor_forw;
        neighbor != (neighbor_entry *) hash_neighbor;
        neighbor = neighbor->neighbor_forw)
    {
        if (neighbor->neighbor_hash != hash)
        {
            continue;
        }

        // address matches with this neighbor entry return it
        if (Address_IsSameAddress(&neighbor->neighbor_main_addr, &dst))
        {
            return neighbor;
        }
    }
    return NULL;
}

double LookupSpecificHopDegreeWRTNodeFromNeighborTable(Node* node, NodeAddress specificHop)
{

	Address aSpeHop;

	SetIPv4AddressInfo(&aSpeHop, specificHop);

	neighbor_entry* neighbor = OlsrLookupNeighborTable(node, aSpeHop);

	return neighbor->neighbor_infos.dDegreeWRTNode;


}

NodeAddress GetSuitableThirdPartyNodeForDirectionAdjust(Node* node, NodeAddress ExpectedNextHop, double * dDiff)
{

	//DebugBreak();

	//printf("GetSuitableThirdPartyNodeForDirectionAdjust start: \n");

	NodeAddress naRet = ANY_IP;

	Address aExpectedNeighbor;

	SetIPv4AddressInfo(&aExpectedNeighbor, ExpectedNextHop);

	neighbor_entry* neighbor = OlsrLookupNeighborTable(node, aExpectedNeighbor);

	if (neighbor == NULL)
	{
		return naRet;
	}


	neighbor_2_list_entry* neigh_2_list;

	neigh_2_list = neighbor->neighbor_2_list;
	while (neigh_2_list != NULL)
	{
		Address n2_addr;
		
		n2_addr = neigh_2_list->neighbor_2->neighbor_2_addr;

		if (n2_addr.interfaceAddr.ipv4 == node->nodeId)
		{
			//continue;
		}
		else
		{
			

			rt_entry* destination;
			rthash* routing_hash;

			UInt32 hash;

			RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

			OlsrHashing(n2_addr, &hash);
			routing_hash = &olsr->routingtable[hash % HASHMASK];


			for (destination = routing_hash->rt_back;
				destination != (rt_entry* ) routing_hash;
				destination = destination->rt_back)
			{
				if (destination->rt_hash != hash)
				{

					continue;
				}


				if (fabs(RadiusDegreeDifference(destination->rt_entry_infos.related_neighbor->neighbor_infos.dDegreeWRTNode, neighbor->neighbor_infos.dDegreeWRTNode)) <= ((double)M_PI / ((double)18))
					|| fabs(RadiusDegreeDifference(neighbor->neighbor_infos.dDegreeWRTNode + (double)M_PI, destination->rt_entry_infos.related_neighbor->neighbor_infos.dDegreeWRTNode)) <= ((double)M_PI / ((double)18))
					)
				{

					break;
				}


				if (destination->rt_entry_infos.rtu_metric == 1)
				{
					*dDiff = RadiusDegreeDifference(destination->rt_entry_infos.related_neighbor->neighbor_infos.dDegreeWRTNode, 
													neighbor->neighbor_infos.dDegreeWRTNode);

					return n2_addr.interfaceAddr.ipv4;
				}


				break;
			

			}

		}
		
		neigh_2_list = neigh_2_list->neighbor_2_next;
	}

	neigh_2_list = neighbor->neighbor_2_list;

	while (neigh_2_list != NULL)
	{
		Address n2_addr;

		n2_addr = neigh_2_list->neighbor_2->neighbor_2_addr;

		if (n2_addr.interfaceAddr.ipv4 == node->nodeId)
		{
			//continue;
		}
		else
		{


			rt_entry* destination;
			rthash* routing_hash;

			UInt32 hash;

			RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

			OlsrHashing(n2_addr, &hash);
			routing_hash = &olsr->routingtable[hash % HASHMASK];


			for (destination = routing_hash->rt_back;
				destination != (rt_entry* ) routing_hash;
				destination = destination->rt_back)
			{
				if (destination->rt_hash != hash)
				{

					continue;
				}


				if (fabs(RadiusDegreeDifference(destination->rt_entry_infos.related_neighbor->neighbor_infos.dDegreeWRTNode, neighbor->neighbor_infos.dDegreeWRTNode)) <= ((double)M_PI / ((double)18))
					|| fabs(RadiusDegreeDifference(neighbor->neighbor_infos.dDegreeWRTNode + (double)M_PI, destination->rt_entry_infos.related_neighbor->neighbor_infos.dDegreeWRTNode)) <= ((double)M_PI / ((double)18))
					)
				{
					//for rtu_metric == 2, need to check every entry with cost 2, so continue
					continue;
				}
				
				if (destination->rt_entry_infos.rtu_metric == 1)
				{
					//since this case must have already returned for former check
					continue;
				}
				
				if (destination->rt_entry_infos.rtu_metric == 2)
				{
					//prove that both the route and the n2_addr on the same part of the straight between currenthop and nexthop !!!!!!!!
					*dDiff = RadiusDegreeDifference(destination->rt_entry_infos.related_neighbor->neighbor_infos.dDegreeWRTNode, 
													neighbor->neighbor_infos.dDegreeWRTNode);
					
					return n2_addr.interfaceAddr.ipv4;
				}

				if (destination->rt_entry_infos.rtu_metric > 2)
				{

					break;
				}
			}
		}

		neigh_2_list = neigh_2_list->neighbor_2_next;

	}


	//printf("GetSuitableThirdPartyNodeForDirectionAdjust end: \n");

	return naRet;
}


// /**
// FUNCTION   :: OlsrReleaseNeighborTable
// LAYER      :: APPLICATION
// PURPOSE    :: Releases neighbor table for this node
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// RETURN :: void : NULL
// **/
static
void OlsrReleaseNeighborTable(
    Node* node)
{
    unsigned char index;
    neighbor_entry* neighbor;
    neighborhash_type* hash_neighbor;

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    for (index = 0; index < HASHSIZE; index++)
    {
        hash_neighbor = &olsr->neighbortable.neighborhash[index];

        for (neighbor = hash_neighbor->neighbor_forw;
            neighbor != (neighbor_entry *) hash_neighbor;
            neighbor = neighbor->neighbor_forw)
        {
            // deletes each neighbor entry
            OlsrDeleteNeighborTable(neighbor);
        }
    }
}

// /**
// FUNCTION   :: OlsrTimeout2HopNeighbors
// LAYER      :: APPLICATION
// PURPOSE    :: This function will be called when NEIGHBOR_HOLD_TIMER
//               expires. Removes two hop neighbors for the  entry for
//               which timer expires
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + neighbor  : neighbor_entry * : Pointer to expired entry
// RETURN :: void : NULL
// **/

static
void OlsrTimeout2HopNeighbors(
    Node* node,
    neighbor_entry* neighbor)
{
    neighbor_2_list_entry* two_hop_list;
    neighbor_2_list_entry* two_hop_list_tmp;
    neighbor_2_entry* two_hop_entry;

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    ERROR_Assert(neighbor, "Invalid neighbor entry");

    two_hop_list = neighbor->neighbor_2_list;
    neighbor->neighbor_2_list = NULL;

    while (two_hop_list != NULL)
    {
        if (getSimTime(node) >= two_hop_list->neighbor_2_timer)
        {
            // expires for current entry
            two_hop_entry = two_hop_list->neighbor_2;
            two_hop_entry->neighbor_2_pointer--;

            OlsrDeleteNeighborPointer(two_hop_entry,
                    neighbor->neighbor_main_addr);

            if (two_hop_entry->neighbor_2_pointer < 1)
            {
                // means this two hop entry is no more pointed, not reachable
                OlsrRemoveList((olsr_qelem *) two_hop_entry);
                MEM_free((void *)two_hop_entry);
            }
            two_hop_list_tmp = two_hop_list;
            two_hop_list = two_hop_list->neighbor_2_next;
            MEM_free(two_hop_list_tmp);

            // This flag is set to TRYE to recalculate the MPR set and the
            // routing table


             	g_iNeighborChgByOlsrTimeout2HopNeighbors++;

            
			//Peter Comment: skip this one, just let it do re-calculation	
			olsr->changes_neighborhood = TRUE;
            olsr->changes_topology = TRUE;

            g_iTopologyChgByOlsrTimeout2HopNeighbors++;
        }
        else
        {
            // not expired, still should be in the list
            two_hop_list_tmp = two_hop_list;
            two_hop_list = two_hop_list->neighbor_2_next;
            two_hop_list_tmp->neighbor_2_next = neighbor->neighbor_2_list;
            neighbor->neighbor_2_list = two_hop_list_tmp;
        }
    }
}

// /**
// FUNCTION   :: OlsrTimeoutNeighborhoodTables
// LAYER      :: APPLICATION
// PURPOSE    :: This function will be called when NEIGHBOR_HOLD_TIMER
//               expires. Removes that entry for which timer expires
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// RETURN :: void : NULL
// **/

static
void OlsrTimeoutNeighborhoodTables(
    Node* node)
{
    unsigned char index;
    neighbor_entry* neighbor;
    neighborhash_type* hash_neighbor;

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    for (index = 0; index < HASHSIZE; index++)
    {
        hash_neighbor = &olsr->neighbortable.neighborhash[index];
        neighbor = hash_neighbor->neighbor_forw;

        while (neighbor != (neighbor_entry *) hash_neighbor)
        {
            OlsrTimeout2HopNeighbors(node, neighbor);
            neighbor = neighbor->neighbor_forw;
        }

    }
}

// /**
// FUNCTION   :: OlsrPrintNeighborTable
// LAYER      :: APPLICATION
// PURPOSE    :: Prints neighbor table
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// RETURN :: void : NULL
// **/

static
void OlsrPrintNeighborTable(
    Node* node)
{
    int index;
    neighbor_entry* neighbor;
    neighborhash_type* hash_neighbor;
    neighbor_2_list_entry* list_2;

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;



	if (g_iRunTimeCompare == 1)
	{
		sprintf(olsr->pszOtherTables, "Neighbor List: \n");
	}
	else
	{
		if (g_iChaseRouteTable == 1)
		{
			//memset(g_szTextRT, 0, 16384 * sizeof(char));

			sprintf(g_szTextRT, "Neighbor List: \n");
		}
		else
		{

			printf("Neighbor List: \n");
		}
	}

	

    

    for (index = 0; index < HASHSIZE; index++)
    {
        hash_neighbor = &olsr->neighbortable.neighborhash[index];

        for (neighbor = hash_neighbor->neighbor_forw;
            neighbor != (neighbor_entry *) hash_neighbor;
            neighbor = neighbor->neighbor_forw)
        {
            char addrString[MAX_STRING_LENGTH];

            IO_ConvertIpAddressToString(&neighbor->neighbor_main_addr,
                                        addrString);

			if (g_iRunTimeCompare == 1)
			{
				sprintf(olsr->pszOtherTables, "%s%-15s %3d [2 hop neighbor: ", olsr->pszOtherTables,
					addrString,
					neighbor->neighbor_status);
			}
			else
			{
				if (g_iChaseRouteTable == 1)
				{
					sprintf(g_szTextRT, "%s%-15s %3d [2 hop neighbor: ", g_szTextRT,
						addrString,
						neighbor->neighbor_status);
				}
				else
				{
					printf("%-15s %3d [2 hop neighbor: ",
						addrString,
						neighbor->neighbor_status);
				}

			}


			
          

            list_2 = neighbor->neighbor_2_list;
            while (list_2 != NULL)
            {
                IO_ConvertIpAddressToString(
                    &list_2->neighbor_2->neighbor_2_addr,
                    addrString);


				if (g_iRunTimeCompare == 1)
				{

					sprintf(olsr->pszOtherTables, "%s%s ",olsr->pszOtherTables, addrString);
				}
				else
				{
					if (g_iChaseRouteTable == 1)
					{ 

						sprintf(g_szTextRT, "%s%s ",g_szTextRT,addrString);
					}
					else
					{

						printf("%s ",addrString);
					}
				}

			

                list_2 = list_2->neighbor_2_next;
            }
            
			if (g_iRunTimeCompare == 1)
			{

				sprintf(olsr->pszOtherTables, "%s]\n", olsr->pszOtherTables);
			}
			else
			{

				if (g_iChaseRouteTable == 1)
				{
					sprintf(g_szTextRT, "%s]\n", g_szTextRT);
				}
				else
				{
					printf("]\n");
				}
			}

				
			
        }
    }
}

// /**
// FUNCTION   :: OlsrDelete2HopNeighborTable
// LAYER      :: APPLICATION
// PURPOSE    :: Delete a two hop neighbor entry results the deletion of its 1
//              hop neighbors list !! We don't try to remove the one hop
//              neighbor even if it has no more 2 hop neighbors !!
// PARAMETERS ::
// + two_hop_neighbor : neighbor_2_entry* : Pointer to two hop neighbor entry
// RETURN :: void : NULL
// **/

void OlsrDelete2HopNeighborTable(
    neighbor_2_entry* two_hop_neighbor)
{
    neighbor_list_entry* one_hop_list;
    neighbor_entry* one_hop_entry;
 
    ERROR_Assert(two_hop_neighbor, "Invalid two hop neighbor entry");

	
    // first delete one hop list of this 2 hop neighbor
    one_hop_list = two_hop_neighbor->neighbor_2_nblist;

    while (one_hop_list != NULL)
    {
        one_hop_entry = one_hop_list->neighbor;

		

        OlsrDeleteNeighbor2Pointer(one_hop_entry,
                two_hop_neighbor->neighbor_2_addr);

        two_hop_neighbor->neighbor_2_nblist = one_hop_list->neighbor_next;
        MEM_free(one_hop_list);
        one_hop_list = two_hop_neighbor->neighbor_2_nblist;
    }

    // deletes 2 hop neighbor
    OlsrRemoveList((olsr_qelem *) two_hop_neighbor);
    MEM_free((void *) two_hop_neighbor);
}


// /**
// FUNCTION   :: OlsrInsert2HopNeighborTable
// LAYER      :: APPLICATION
// PURPOSE    :: Inserts a two hop neighbor entry in the neighbor table
// PARAMETERS ::
// + two_hop_neighbor : neighbor_2_entry* : Pointer to two hop neighbor entry
// RETURN :: void : NULL
// **/

static
void OlsrInsert2HopNeighborTable(
    Node *node,
    neighbor_2_entry *two_hop_neighbor)
{
    UInt32 hash;
    neighbor2_hash* hash_two_neighbor;

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    ERROR_Assert(two_hop_neighbor, "Invalid two hop neighbor entry");

    OlsrHashing(two_hop_neighbor->neighbor_2_addr, &hash);

    two_hop_neighbor->neighbor_2_hash = hash;
    hash_two_neighbor = &olsr->neighbor2table[hash % HASHMASK];

    OlsrInsertList((olsr_qelem *)two_hop_neighbor,
            (olsr_qelem *)hash_two_neighbor);
}

// /**
// FUNCTION   ::  OlsrLookup2HopNeighborTable
// LAYER      :: APPLICATION
// PURPOSE    :: Searches an address in the two hop neighbor table
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + dest : Address: address to be searched
// RETURN :: neighbor_2_entry* : Pointer to entry if found, else NULL
// **/

neighbor_2_entry* OlsrLookup2HopNeighborTable(
    Node *node,
    Address dest)
{
    neighbor_2_entry* neighbor_2;
    neighbor2_hash* hash_2_neighbor;
    UInt32 hash;
    mid_address* addr;
    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    OlsrHashing(dest, &hash);
    hash_2_neighbor = &olsr->neighbor2table[hash % HASHMASK];

    for (neighbor_2 = hash_2_neighbor->neighbor2_forw;
        neighbor_2 != (neighbor_2_entry *) hash_2_neighbor;
        neighbor_2 = neighbor_2->neighbor_2_forw)
    {
        if (neighbor_2->neighbor_2_hash != hash)
        {
            continue;
        }

        // searches in the neighbor 2 table
        if (Address_IsSameAddress(&neighbor_2->neighbor_2_addr, &dest))
        {
            return(neighbor_2);
        }

        addr = OlsrLookupMidAliases(node, neighbor_2->neighbor_2_addr);
        while (addr)
        {
            if (Address_IsSameAddress(&addr->alias, &dest))
            {
                return neighbor_2;
            }
            addr = addr->next_alias;
        }
    }
    return NULL;
}

// /**
// FUNCTION   :: OlsrRelease2HopNeighborTable
// LAYER      :: APPLICATION
// PURPOSE    :: Releases the two hop neighbor table for this node
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// RETURN :: void : NULL
// **/

static
void OlsrRelease2HopNeighborTable(
    Node* node)
{
    Int32 index;
    neighbor_2_entry* neighbor_2;
    neighbor_2_entry* neighbor_2_tmp;
    neighbor2_hash* hash_2_neighbor;

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    for (index = 0; index < HASHSIZE; index++)
    {
        hash_2_neighbor = &olsr->neighbor2table[index];
        neighbor_2 = hash_2_neighbor->neighbor2_forw;

        while (neighbor_2 != (neighbor_2_entry *) hash_2_neighbor)
        {
            neighbor_2_tmp = neighbor_2;
            neighbor_2 = neighbor_2->neighbor_2_forw;
            OlsrDelete2HopNeighborTable(neighbor_2_tmp);
        }
    }
}


// /**
// FUNCTION   :: OlsrPrint2HopNeighborTable
// LAYER      :: APPLICATION
// PURPOSE    :: Prints the two hop neighbor table for this node
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// RETURN :: void : NULL
// **/

static
void OlsrPrint2HopNeighborTable(Node *node)
{
    Int32 index;
    neighbor_2_entry* neighbor_2;
    neighbor2_hash* hash_2_neighbor;

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    neighbor_list_entry* list_1 = NULL;


	if (g_iRunTimeCompare == 1)
	{
		sprintf(olsr->pszOtherTables, "Two Hop Neighbors\n");
	}
	else
	{
		if (g_iChaseRouteTable == 1)
		{
			memset(g_szTextRT, 0, 16384 * sizeof(char));

			sprintf(g_szTextRT, "Two Hop Neighbors\n");
		}
		else
		{

			printf("Two Hop Neighbors\n");
		}
	}

	


    for (index = 0; index < HASHSIZE; index++)
    {
        hash_2_neighbor = &olsr->neighbor2table[index];
        for (neighbor_2 = hash_2_neighbor->neighbor2_forw;
            neighbor_2 != (neighbor_2_entry *) hash_2_neighbor;
            neighbor_2 = neighbor_2->neighbor_2_forw)
        {
            char addrString[MAX_STRING_LENGTH];

            IO_ConvertIpAddressToString(&neighbor_2->neighbor_2_addr,
                                        addrString);


			if (g_iRunTimeCompare == 1)
			{
				
				sprintf(olsr->pszOtherTables, "%s%s ", olsr->pszOtherTables, addrString);
			}
			else
			{
				if (g_iChaseRouteTable == 1)
				{

					sprintf(g_szTextRT, "%s%s ",g_szTextRT, addrString);
				}	
				else
				{

					printf("%s ",addrString);
				}
			}
			

            list_1 = neighbor_2->neighbor_2_nblist;

			
			if (g_iRunTimeCompare == 1)
			{
				sprintf(olsr->pszOtherTables, "%spointed by  ", olsr->pszOtherTables);
			}
			else
			{
				if (g_iChaseRouteTable == 1)
				{

					sprintf(g_szTextRT, "%spointed by  ", g_szTextRT);
				}	
				else
				{

					printf("pointed by ");
				}
			}
			
			


            
            while (list_1 != NULL)
            {
                IO_ConvertIpAddressToString(
                    &list_1->neighbor->neighbor_main_addr,
                    addrString);


				if (g_iRunTimeCompare == 1)
				{
					sprintf(olsr->pszOtherTables, "%s%s ", olsr->pszOtherTables, addrString);
				}
				else
				{
					if (g_iChaseRouteTable == 1)
					{
						sprintf(g_szTextRT, "%s%s ", g_szTextRT, addrString);
					}
					else
					{
						printf("%s ", addrString);
					}
				}

				

                
                list_1 = list_1->neighbor_next;
            }


			if (g_iRunTimeCompare == 1)
			{
				sprintf(olsr->pszOtherTables, "%s\n", olsr->pszOtherTables);
			}
			else
			{
				if (g_iChaseRouteTable == 1)
				{
					sprintf(g_szTextRT, "%s\n", g_szTextRT);
				}
				else
				{
					printf("\n");
				}
			}
			

            
        }
    }
}


// /**
// FUNCTION   :: OlsrClear2HopProcessed
// LAYER      :: APPLICATION
// PURPOSE    :: Function to clear processed status of 2 hop neighbors
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// RETURN :: void : NULL
// **/

static
void OlsrClear2HopProcessed(
    Node* node)
{
   neighbor_2_entry* neighbor_2;
   neighbor2_hash* hash_2_neighbor;

   unsigned char index;
   RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

   for (index = 0; index < HASHSIZE; index++)
   {
       hash_2_neighbor = &olsr->neighbor2table[index];

       for (neighbor_2 = hash_2_neighbor->neighbor2_forw;
            neighbor_2 != (neighbor_2_entry  *) hash_2_neighbor;
            neighbor_2 = neighbor_2->neighbor_2_forw)
       {
           // Clear
           neighbor_2->processed = 0;
       }

   }
}


// /**
// FUNCTION   :: OlsrFind2HopNeighborsWith1Link
// LAYER      :: APPLICATION
// PURPOSE    :: Finds the two hop neighbor with 1 link for this node
//               with specified willingness
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + willingness: Int32: willingess value to be searched
// RETURN :: neighbor_2_list_entry : List of 2 hop neighbors satisfying
// criteria
// **/

static
neighbor_2_list_entry* OlsrFind2HopNeighborsWith1Link(
    Node* node,
    Int32 willingness)
{
    Int32 index;
    neighbor_2_list_entry* two_hop_list_tmp = NULL;
    neighbor_2_list_entry* two_hop_list = NULL;
    neighbor_2_entry* two_hop_neighbor = NULL;
    neighbor_entry* dup_neighbor;
    neighbor2_hash* hash_2_neighbor;

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    for (index = 0; index < HASHSIZE; index++)
    {
        hash_2_neighbor = &olsr->neighbor2table[index];

        for (two_hop_neighbor = hash_2_neighbor->neighbor2_forw;
            two_hop_neighbor != (neighbor_2_entry  *) hash_2_neighbor;
            two_hop_neighbor = two_hop_neighbor->neighbor_2_forw)
        {
            // two_hop_neighbor->neighbor_2_state = 0;
            dup_neighbor = OlsrLookupNeighborTable(node,
                               two_hop_neighbor->neighbor_2_addr);

            if ((dup_neighbor!=NULL)
                && (dup_neighbor->neighbor_status != NOT_SYM))
            {
                continue;
            }

            if (two_hop_neighbor->neighbor_2_pointer == 1)
            {
                if ((two_hop_neighbor->neighbor_2_nblist->neighbor->
                    neighbor_status == SYM_NEIGH)
                    && (two_hop_neighbor->neighbor_2_nblist->neighbor->
                            neighbor_willingness == willingness))
                {
                    two_hop_list_tmp = (neighbor_2_list_entry *)
                            MEM_malloc(sizeof(neighbor_2_list_entry));

                    memset(
                        two_hop_list_tmp,
                        0,
                        sizeof(neighbor_2_list_entry));

                    two_hop_list_tmp->neighbor_2 = two_hop_neighbor;
                    two_hop_list_tmp->neighbor_2_next = two_hop_list;
                    two_hop_list = two_hop_list_tmp;
                }
            }
        }
    }
    // return 2 hop neighbor 2 list
    return(two_hop_list_tmp);
}

// /**
// FUNCTION   :: OlsrCalculateNeighbors
// LAYER      :: APPLICATION
// PURPOSE    :: This function calculates the number of second hop neighbors for
//               each neighbor
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + two_hop_count : UInt16* : Pointer to the counter to be filled
// RETURN :: void : NULL
// **/

static
void OlsrCalculateNeighbors(
    Node* node,
    UInt16* two_hop_count)
{
    int index;
    neighborhash_type* neighbor_hash_table;
    neighbor_entry* a_neighbor;
    UInt16 n_count = 0;
    UInt16 sum = 0;
    UInt16 count = 0;
    neighbor_entry* dup_neighbor;

    OlsrClear2HopProcessed(node);

    neighbor_2_list_entry* twohop_neighbors;

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    neighbor_hash_table = olsr->neighbortable.neighborhash;

    for (index = 0; index < HASHSIZE; index++)
    {
        for (a_neighbor = neighbor_hash_table[index].neighbor_forw;
            a_neighbor != (neighbor_entry  *)&neighbor_hash_table[index];
            a_neighbor = a_neighbor->neighbor_forw)
        {
            count = 0;
            n_count = 0;

            if (a_neighbor->neighbor_status == NOT_SYM)
            {
                a_neighbor->neighbor_2_nocov = count;
                continue;
            }

            twohop_neighbors = a_neighbor->neighbor_2_list;
            while (twohop_neighbors != NULL)
            {
                dup_neighbor = OlsrLookupNeighborTable(node,
                                   twohop_neighbors->neighbor_2->
                                                 neighbor_2_addr);

                if ((dup_neighbor == NULL)
                     || (dup_neighbor->neighbor_status != SYM))
                {
                    n_count++;
                    if (!twohop_neighbors->neighbor_2->processed)
                    {
                        count++;
                        twohop_neighbors->neighbor_2->processed = 1;
                    }
                }

                twohop_neighbors = twohop_neighbors->neighbor_2_next;
            }

            a_neighbor->neighbor_2_nocov = n_count;
            sum = sum + count;
        }
    }
    *two_hop_count = (UInt16) (*two_hop_count + sum);
}

// /**
// FUNCTION   :: OlsrLinkingThis2Entries
// LAYER      :: APPLICATION
// PURPOSE    :: This function links 2 hop neighbor to neighbor entry
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + neighbor : neighbor_entry *:  Pointer to neighbor entry
// + two_hop_neighbor: neighbor_2_entry * : Pointer to 2 hop neighbor entry
// RETURN :: void : NULL
// **/

static
void OlsrLinkingThis2Entries(
    Node* node,
    neighbor_entry* neighbor,
    neighbor_2_entry* two_hop_neighbor,
    float vtime)
{
    neighbor_list_entry* list_of_1_neighbors;
    neighbor_2_list_entry* list_of_2_neighbors;

    ERROR_Assert(neighbor, "Invalid neighbor entry");
    ERROR_Assert(two_hop_neighbor, "Invalid two hop neighbor entry");

    list_of_1_neighbors = (neighbor_list_entry *)
            MEM_malloc(sizeof(neighbor_list_entry));

    memset(list_of_1_neighbors, 0, sizeof(neighbor_list_entry));

    list_of_2_neighbors = (neighbor_2_list_entry *)
            MEM_malloc(sizeof(neighbor_2_list_entry));

    memset(list_of_2_neighbors, 0, sizeof(neighbor_2_list_entry));

    list_of_1_neighbors->neighbor = neighbor;
    list_of_1_neighbors->neighbor_next = two_hop_neighbor->neighbor_2_nblist;

    two_hop_neighbor->neighbor_2_nblist = list_of_1_neighbors;

    list_of_2_neighbors->neighbor_2 = two_hop_neighbor;

    list_of_2_neighbors->neighbor_2_timer =
        getSimTime(node) + (clocktype)(vtime * SECOND);

    list_of_2_neighbors->neighbor_2_next = neighbor->neighbor_2_list;

    neighbor->neighbor_2_list = list_of_2_neighbors;

    // increment the pointer counter
    two_hop_neighbor->neighbor_2_pointer++;
}


/***************************************************************************
 *                 Definition of MPR Selector Table                        *
 ***************************************************************************/

// /**
// FUNCTION   :: OlsrDeleteMprSelectorTable
// LAYER      :: APPLICATION
// PURPOSE    :: Deletes entry from MPR  selector table
// PARAMETERS ::
// + mprs : mpr_selector_entry *:  Pointer to mpr entry
// RETURN :: void : NULL
// **/

void OlsrDeleteMprSelectorTable(
    mpr_selector_entry* mprs)
{
    OlsrRemoveList((olsr_qelem*) mprs);
    MEM_free((void*) mprs);
}


// /**
// FUNCTION   :: OlsrClearMprs
// LAYER      :: APPLICATION
// PURPOSE    :: Clear all  neighbors' MPR status
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// RETURN :: void : NULL
// **/

static
void  OlsrClearMprs(
    Node* node)
{
   unsigned char index;
   neighbor_entry* a_neighbor;
   neighbor_2_list_entry* two_hop_list;
   neighborhash_type* neighbor_hash_table;

   RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;
   neighbor_hash_table = olsr->neighbortable.neighborhash;

   for (index = 0; index < HASHSIZE; index++)
   {
       for (a_neighbor = neighbor_hash_table[index].neighbor_forw;
               a_neighbor != (neighbor_entry  *)&neighbor_hash_table[index];
               a_neighbor = a_neighbor->neighbor_forw)
       {
           // Clear MPR selection
           if (a_neighbor->neighbor_is_mpr)
           {
               a_neighbor->neighbor_was_mpr = true;
               a_neighbor->neighbor_is_mpr = false;
           }

           // Clear two hop neighbors coverage count
           for (two_hop_list = a_neighbor->neighbor_2_list;
                   two_hop_list != NULL;
                   two_hop_list = two_hop_list->neighbor_2_next)
           {
               two_hop_list->neighbor_2->mpr_covered_count = 0;
           }
       }

   }
}

// /**
// FUNCTION   :: OlsrInsertMprSelectorTable
// LAYER      :: APPLICATION
// PURPOSE    :: Inserts entry in MPR  selector table
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + mprs : mpr_selector_entry* :  Pointer to entry
// RETURN :: void : NULL
// **/

static
void OlsrInsertMprSelectorTable(
    Node* node,
    mpr_selector_entry* mprs)
{
    UInt32  hash;
    mpr_selector_hash_type* mprs_hash;

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    ERROR_Assert(mprs, "Invalid MPR selector entry");

    OlsrHashing(mprs->mpr_selector_main_addr, &hash);
    mprs->mprselector_hash = hash;

    mprs_hash = &olsr->mprstable.mpr_selector_hash[hash % HASHMASK];

    // inserts new entry in the table
    OlsrInsertList((olsr_qelem *)mprs, (olsr_qelem *)mprs_hash);
}


// /**
// FUNCTION   :: OlsrLookupMprSelectorTable
// LAYER      :: APPLICATION
// PURPOSE    :: Search an address in the MPR  selector table
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + dst  : Address : Address to be searched
// RETURN :: mpr_selector_entry* : Pointer to entry if found, else NULL
// **/
mpr_selector_entry* OlsrLookupMprSelectorTable(
    Node* node,
    Address dst)
{
    mpr_selector_entry* mprs;
    mpr_selector_hash_type* mprs_hash;
    UInt32 hash;

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    OlsrHashing(dst, &hash);
    mprs_hash = &olsr->mprstable.mpr_selector_hash[hash % HASHMASK];

    for (mprs = mprs_hash->mpr_selector_forw;
        mprs != (mpr_selector_entry *) mprs_hash;
        mprs = mprs->mpr_selector_forw)
    {
        if (mprs->mprselector_hash != hash)
        {
            continue;
        }

        // try to match the address with the selector address from MPR entry
        if (Address_IsSameAddress(&mprs->mpr_selector_main_addr, &dst))
        {
            // match found
            return mprs;
        }
    }
    // no match return NULL
    return NULL;
}


// /**
// FUNCTION   :: OlsrUpdateMprSelectorTable
// LAYER      :: APPLICATION
// PURPOSE    :: Updates MPR selector table entry vtime
//               Adds a new entry if no entry exists
//               and sets the vtime
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + addr : Address : Address of node to be updated
// + vtime: float : validity time of entry in seconds
// RETURN :: void : NULL
// **/

static
void OlsrUpdateMprSelectorTable (
    Node* node,
    Address addr,
    float vtime)
{
    mpr_selector_entry* mprs;
    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    // search current source address from hello message in the MPR table
    if ((mprs = OlsrLookupMprSelectorTable(
                    node, addr)) == NULL)
    {
        // not found in the table, going to create a new one
        mprs = (mpr_selector_entry *)
            MEM_malloc(sizeof (mpr_selector_entry));

        memset(mprs, 0, sizeof(mpr_selector_entry));

        // mpr selector address set by the message source address
        mprs->mpr_selector_main_addr = addr;
        mprs->mpr_selector_timer =
            getSimTime(node) + (clocktype)(vtime * SECOND);

        OlsrInsertMprSelectorTable(node, mprs);

        // increment mssn no. don't forget to increment this n. on timeout
        olsr->mprstable.ansn++;
    }
    else
    {
        mprs->mpr_selector_timer =
                getSimTime(node) + (clocktype)(vtime * SECOND);
    }
}

// /**
// FUNCTION   :: OlsrReleaseMprSelectorTable
// LAYER      :: APPLICATION
// PURPOSE    :: Releases MPR selector table for this node
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// RETURN :: void : NULL
// **/

static
void OlsrReleaseMprSelectorTable(
    Node* node)
{
    mpr_selector_entry* mprs;
    mpr_selector_entry* mprs_tmp;
    mpr_selector_hash_type* mprs_hash;
    int index;

    RoutingOlsr *olsr = (RoutingOlsr* ) node->appData.olsr;

    for (index = 0; index < HASHSIZE; index++)
    {
        mprs_hash = &olsr->mprstable.mpr_selector_hash[index];

        mprs = mprs_hash->mpr_selector_forw;

        while (mprs != (mpr_selector_entry *) mprs_hash)
        {
            // delete each MPR entry
            mprs_tmp = mprs;
            mprs = mprs->mpr_selector_forw;
            OlsrDeleteMprSelectorTable(mprs_tmp);
        }
    }
}

// /**
// FUNCTION   :: OlsrExistMprSelectorTable
// LAYER      :: APPLICATION
// PURPOSE    :: Check whether there is an entry in the MPR selctor table
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// RETURN :: BOOL : TRUE if non-empty, else FALSE
// **/

static
BOOL OlsrExistMprSelectorTable(
    Node* node)
{
    mpr_selector_entry* mprs;
    mpr_selector_hash_type* mprs_hash;
    int index;

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    for (index = 0; index < HASHSIZE; index++)
    {
        mprs_hash = &olsr->mprstable.mpr_selector_hash[index];

        mprs = mprs_hash->mpr_selector_forw;
        while(mprs != (mpr_selector_entry *)mprs_hash)
        {
            mprs = mprs->mpr_selector_forw;
        }
        if (mprs == (mpr_selector_entry *)mprs_hash)
        {
            return TRUE;
        }
    }
    return FALSE;
}

// /**
// FUNCTION   :: OlsrTimeoutMprSelectorTable
// LAYER      :: APPLICATION
// PURPOSE    :: This function will be called when NEIGHBOR_HOLD_TIMER
//               expires and removes that MPR selector entry that is
//               invalid w.r.t. current time
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// RETURN :: void : NULL
// **/

static
void OlsrTimeoutMprSelectorTable(
    Node* node)
{
    mpr_selector_entry* mprs;
    mpr_selector_entry* mprs_tmp;
    mpr_selector_hash_type* mprs_hash;
    int index;

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    for (index = 0; index < HASHSIZE; index++)
    {
        mprs_hash = &olsr->mprstable.mpr_selector_hash[index];
        mprs = mprs_hash->mpr_selector_forw;

        while (mprs != (mpr_selector_entry *) mprs_hash)
        {
            // current time is more than the valid hold time
            if (getSimTime(node) >= mprs->mpr_selector_timer)
            {
                mprs_tmp = mprs;
                mprs = mprs->mpr_selector_forw;
                OlsrDeleteMprSelectorTable(mprs_tmp);

                // increment mssn no. don't forget to increment this number
                olsr->mprstable.ansn++;
            }
            else
            {
                mprs = mprs->mpr_selector_forw;
            }
        }
    }
}

// /**
// FUNCTION   :: OlsrPrintMprSelectorTable
// LAYER      :: APPLICATION
// PURPOSE    :: Prints MPR selector table for this node
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// RETURN :: void : NULL
// **/

static
void OlsrPrintMprSelectorTable(
    Node* node)
{
    mpr_selector_entry* mprs;
    mpr_selector_hash_type* mprs_hash;
    int index;

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    printf("Mpr Selector Table: [");
    for (index = 0; index < HASHSIZE; index++)
    {
        mprs_hash = &olsr->mprstable.mpr_selector_hash[index];

        for (mprs = mprs_hash->mpr_selector_forw;
            mprs != (mpr_selector_entry *) mprs_hash;
            mprs = mprs->mpr_selector_forw)
        {
            char addrString[MAX_STRING_LENGTH];

            IO_ConvertIpAddressToString(&mprs->mpr_selector_main_addr,
                                        addrString);

            printf("%s ", addrString);
        }
    }
    printf("]\n");
}

// /**
// FUNCTION   :: OlsrFindMaximumCovered
// LAYER      :: APPLICATION
// PURPOSE    :: This function calculates maximum covered neighbor entry
//               for a specified willingness
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + willingness: Int32 : willingness of the node
// RETURN :: neighbor_entry* : pointer to neighbor entry if found, else
//           NULL
// **/

static
neighbor_entry* OlsrFindMaximumCovered(
    Node* node,
    Int32 willingness)
{
    UInt16 maximum = 0;
    int index;
    neighborhash_type* neighbor_hash_table;
    neighbor_entry* a_neighbor;
    neighbor_entry* mpr_candidate = NULL;

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    neighbor_hash_table = olsr->neighbortable.neighborhash;

    for (index = 0; index < HASHSIZE; index++)
    {
        for (a_neighbor = neighbor_hash_table[index].neighbor_forw;
            a_neighbor != (neighbor_entry  *)&neighbor_hash_table[index];
            a_neighbor = a_neighbor->neighbor_forw)
        {
            if ((!a_neighbor->neighbor_is_mpr)
                    && (a_neighbor->neighbor_willingness == willingness)
                    && (maximum < a_neighbor->neighbor_2_nocov))
            {
                maximum = (UInt16) (a_neighbor->neighbor_2_nocov);
                mpr_candidate = a_neighbor;
            }
        }
    }
    return mpr_candidate;
}

// /**
// FUNCTION   :: OlsrChosenMpr
// LAYER      :: APPLICATION
// PURPOSE    :: This function  processes the chosen MPR and updates the
//               counters used in calculations
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + one_hop_neighbor : neighbor_entry* :  Pointer to neighbor entry
// + two_hop_covered_count : UInt16* : Pointer to counter
//                                             which counts number of 2 hop
//                                             neighbors covered
// RETURN :: void : NULL
// **/

static
void OlsrChosenMpr(
    Node* node,
    neighbor_entry* one_hop_neighbor,
    UInt16* two_hop_covered_count)
{
    neighbor_list_entry* the_one_hop_list;
    neighbor_2_list_entry* second_hop_entries;
    UInt16 count = 0;
    neighbor_entry* dup_neighbor;

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    ERROR_Assert(one_hop_neighbor, "Invalid neighbor entry");

    count = *two_hop_covered_count;

    if (DEBUG)
    {
        char addrString[MAX_STRING_LENGTH];
        IO_ConvertIpAddressToString(&one_hop_neighbor->neighbor_main_addr,
                addrString);

        printf("Selecting  mpr as %s\n", addrString);
    }

    // set link status of one hop neighbor to MPR
    one_hop_neighbor->neighbor_is_mpr = true;

    second_hop_entries = one_hop_neighbor->neighbor_2_list;

    while (second_hop_entries != NULL)
    {

        dup_neighbor = OlsrLookupNeighborTable(node,
                           second_hop_entries->neighbor_2->neighbor_2_addr);

        if ((dup_neighbor != NULL) && (dup_neighbor->neighbor_status==SYM))
        {

            second_hop_entries = second_hop_entries->neighbor_2_next;
            continue;
        }

        // Now the neighbor is covered by this mpr

        second_hop_entries->neighbor_2->mpr_covered_count++;

        the_one_hop_list =
                second_hop_entries->neighbor_2->neighbor_2_nblist;

        if (second_hop_entries->neighbor_2->mpr_covered_count
            == olsr->mpr_coverage)
        {
            count ++;
        }

        while (the_one_hop_list != NULL)
        {
            if (the_one_hop_list->neighbor->neighbor_status == SYM)
            {
                if (second_hop_entries->neighbor_2->mpr_covered_count
                        >= olsr->mpr_coverage)
                {
                    the_one_hop_list->neighbor->neighbor_2_nocov--;
                }
            }
            the_one_hop_list = the_one_hop_list->neighbor_next;
        }

        second_hop_entries = second_hop_entries->neighbor_2_next;
    }

    *two_hop_covered_count = (UInt16)count;
}


// /**
// FUNCTION   :: OlsrAddWillAlwaysNodes
// LAYER      :: APPLICATION
// PURPOSE    :: Adds all willing nodes which are symmetric to MPR candidate set
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// RETURN :: UInt16 : number of nodes considered
// **/

static
UInt16 OlsrAddWillAlwaysNodes(
    Node* node)
{
    unsigned char index;
    neighbor_entry* a_neighbor;
    UInt16 count;
    count = 0;
    neighborhash_type* hash_neighbor;

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    for (index = 0; index < HASHSIZE; index++)
    {
        hash_neighbor = &olsr->neighbortable.neighborhash[index];

        for (a_neighbor = hash_neighbor->neighbor_forw;
            a_neighbor != (neighbor_entry *) hash_neighbor;
            a_neighbor = a_neighbor->neighbor_forw)
        {

            if ((a_neighbor->neighbor_status == NOT_SYM)
                 || (a_neighbor->neighbor_willingness != WILL_ALWAYS))
            {
                continue;
            }

            OlsrChosenMpr(node, a_neighbor, &count);

        }

    }

    return count;
}

// /**
// FUNCTION   :: OlsrCalculateMpr
// LAYER      :: APPLICATION
// PURPOSE    :: Calculate MPR neighbors for current node
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// RETURN :: void : NULL
// **/

static
void OlsrCalculateMpr(
    Node* node)
{
    UInt16 two_hop_covered_count = 0;
    UInt16 two_hop_count = 0;
    neighbor_2_list_entry *two_hop_list = NULL;
    neighbor_2_list_entry *tmp;
    neighbor_entry* mprs;
    Int32 i;

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    OlsrClearMprs(node);

    OlsrCalculateNeighbors(node, &two_hop_count);

    two_hop_covered_count = OlsrAddWillAlwaysNodes(node);

    // RFC 3626  Section 8.3.1
    // Calculate MPRs based on willingness

    for (i = WILL_ALWAYS - 1; i > WILL_NEVER; i--)
    {
        two_hop_list = OlsrFind2HopNeighborsWith1Link(node, i);

        if (DEBUG)
        {
            printf(" Two hop count: %d\n",two_hop_count);
        }

        // if a node has two hop neighbor then it goes to select corresponding
        // one hop neighbor as MPR

        while (two_hop_list != NULL)
        {
            if (!two_hop_list->neighbor_2->neighbor_2_nblist->
                     neighbor->neighbor_is_mpr)
            {
                OlsrChosenMpr(node,
                    two_hop_list->neighbor_2->neighbor_2_nblist->neighbor,
                    &two_hop_covered_count);
            }
            tmp = two_hop_list;
            two_hop_list = two_hop_list->neighbor_2_next;
            MEM_free(tmp);
        }

        if (DEBUG)
        {
            printf(" Two hops covered: %d\n",two_hop_covered_count);
        }

        if (two_hop_covered_count >= two_hop_count)
        {
            i = WILL_NEVER;
            break;
        }

        while ((mprs = OlsrFindMaximumCovered(node,i)) != NULL)
        {
            OlsrChosenMpr(node, mprs, &two_hop_covered_count);

            if (two_hop_covered_count >= two_hop_count)
            {
                i = WILL_NEVER;
                break;
            }
        }
    }

    // increment the mpr sequence number
    olsr->neighbortable.neighbor_mpr_seq++;
}


/***************************************************************************
 *                 Hello Message Processing                                *
 ***************************************************************************/

// /**
// FUNCTION   :: OlsrDestroyHelloMessage
// LAYER      :: APPLICATION
// PURPOSE    :: Deletes Hello message working structure
// PARAMETERS ::
// + message : hl_message* : Pointer to Hello Message
// RETURN :: void : NULL
// **/

static
void OlsrDestroyHelloMessage(
    hl_message* message)
{
    hello_neighbor* neighbors;
    hello_neighbor* neighbors_tmp;

    ERROR_Assert(message, "Invalid Hello message");

    neighbors = message->neighbors;

    while (neighbors != NULL)
    {
        neighbors_tmp = neighbors;
        neighbors = neighbors->next;
        MEM_free(neighbors_tmp);
    }
}


// /**
// FUNCTION   :: OlsrPrintHelloMessage
// LAYER      :: APPLICATION
// PURPOSE    :: Prints Hello message working structure
// PARAMETERS ::
// + message : hl_message* : Pointer to Hello Message
// RETURN :: void : NULL
// **/

static
void OlsrPrintHelloMessage(
    hl_message* message)
{
    hello_neighbor* neighbors;

    char addrString[MAX_STRING_LENGTH];

    IO_ConvertIpAddressToString(&message->source_addr,
                                addrString);
    neighbors = message->neighbors;

    printf("HELLO Message Content:: \n");
    printf("%s [neighbors:", addrString);

    while (neighbors != NULL)
    {
        IO_ConvertIpAddressToString(&neighbors->address,
                                    addrString);

        printf("%s ", addrString);
        printf("Link: %d Status: %d ", neighbors->link, neighbors->status);

        neighbors = neighbors->next;
    }
    printf("]\n");
}

// /**
// FUNCTION   :: OlsrPrintTcMessage
// LAYER      :: APPLICATION
// PURPOSE    :: Prints Tc message working structure
// PARAMETERS ::
// + message: tc_message * : Pointer to TC Message
// RETURN :: void : NULL
// **/

static
void OlsrPrintTcMessage(
    tc_message* message)
{
    tc_mpr_addr  *mpr;

    char addrString1[MAX_STRING_LENGTH];
    char addrString2[MAX_STRING_LENGTH];

    IO_ConvertIpAddressToString(&message->source_addr,
                                addrString1);

    IO_ConvertIpAddressToString(&message->originator,
                                addrString2);

    mpr = message->multipoint_relay_selector_address;

    printf("TC Message Content::\n");

    printf("Source = %s Orig = %s Seq = %d Hop = %d ansn = %d [",
            addrString1,
            addrString2,
            message->packet_seq_number,
            message->hop_count,
            message->ansn);

    while (mpr != NULL)
    {
        IO_ConvertIpAddressToString(&mpr->address,
                                    addrString1);

        printf("%s ", addrString1);
        mpr = mpr->next;
    }
    printf("]\n");
}

// /**
// FUNCTION   :: OlsrDestroyTcMessage
// LAYER      :: APPLICATION
// PURPOSE    :: Deletes TC message working structure
// PARAMETERS ::
// + message : tc_message* : Pointer to TC Message
// RETURN :: void : NULL
// **/

static
void OlsrDestroyTcMessage(
    tc_message* message)
{
    tc_mpr_addr* mpr_set;
    tc_mpr_addr* mpr_set_tmp;

    mpr_set = message->multipoint_relay_selector_address;

    while (mpr_set != NULL)
    {
        mpr_set_tmp = mpr_set;
        mpr_set = mpr_set->next;
        MEM_free(mpr_set_tmp);
    }
}

// /**
// FUNCTION   :: OlsrSendonAllInterfaces
// LAYER      :: APPLICATION
// PURPOSE    :: Send olsr packet to the UDP layer on all interfaces
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + msg : olsrpacket* : OLSR packet to be sent
// + packetsize : Int32 : Size of packet
// + jitter : clocktype : jitter to be added to packet
// RETURN :: void : NULL
// **/

static
void OlsrSendonAllInterfaces(
    Node* node,
    olsrpacket* msg,
    Int32 packetsize,
    clocktype jitter)
{

    unsigned char index;

    clocktype delay;

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    for (index = 0; index < node->numberInterfaces; index ++ )
    {
        Address interfaceAddr;
        interfaceAddr.networkType = NETWORK_IPV4;


        if (NetworkIpGetInterfaceType(node, index) != olsr->ip_version
            && NetworkIpGetInterfaceType(node, index)!= NETWORK_DUAL)
        {
            continue;
        }

        if(olsr->ip_version == NETWORK_IPV6)
        {
            interfaceAddr.networkType = NETWORK_IPV6;
            Ipv6GetGlobalAggrAddress(
                    node,
                    index,
                    &interfaceAddr.interfaceAddr.ipv6);
        }
        else if (olsr->ip_version == NETWORK_IPV4)
        {
            interfaceAddr.networkType = NETWORK_IPV4;
            interfaceAddr.interfaceAddr.ipv4 =
                            NetworkIpGetInterfaceAddress(node,index);
        }
//#endif

        // set msg->seq no with the  seq no for that interface
        msg->olsr_pack_seq_no = olsr->interfaceSequenceNumbers[index]++;
        delay = (clocktype) (jitter * RANDOM_erand(olsr->seed));

        if (interfaceAddr.networkType == NETWORK_IPV6)
        {
            Address multicastAddr;
            multicastAddr.interfaceAddr.ipv6.s6_addr8[0] = 0xff;
            multicastAddr.interfaceAddr.ipv6.s6_addr8[1] = 0x0e;
            multicastAddr.interfaceAddr.ipv6.s6_addr8[2] = 0x00;
            multicastAddr.interfaceAddr.ipv6.s6_addr8[3] = 0x00;
            multicastAddr.interfaceAddr.ipv6.s6_addr8[4] = 0x00;
            multicastAddr.interfaceAddr.ipv6.s6_addr8[5] = 0x00;
            multicastAddr.interfaceAddr.ipv6.s6_addr8[6] = 0x00;
            multicastAddr.interfaceAddr.ipv6.s6_addr8[7] = 0x00;
            multicastAddr.interfaceAddr.ipv6.s6_addr8[8] = 0x00;
            multicastAddr.interfaceAddr.ipv6.s6_addr8[9] = 0x00;
            multicastAddr.interfaceAddr.ipv6.s6_addr8[10] = 0x00;
            multicastAddr.interfaceAddr.ipv6.s6_addr8[11] = 0x00;
            multicastAddr.interfaceAddr.ipv6.s6_addr8[12] = 0x00;
            multicastAddr.interfaceAddr.ipv6.s6_addr8[13] = 0x00;
            multicastAddr.interfaceAddr.ipv6.s6_addr8[14] = 0x00;
            multicastAddr.interfaceAddr.ipv6.s6_addr8[15] = 0x01;
            multicastAddr.networkType = NETWORK_IPV6;

            APP_UdpSendNewDataWithPriority(
                node,
                APP_ROUTING_OLSR_INRIA,
                interfaceAddr,
                APP_ROUTING_OLSR_INRIA,
                multicastAddr,
                index,
                (char *) msg,
                packetsize,
                IPTOS_PREC_INTERNETCONTROL,
                delay,
                TRACE_OLSR);
        }
        else

        {
            APP_UdpSendNewDataWithPriority(
                node,
                APP_ROUTING_OLSR_INRIA,
                GetIPv4Address(interfaceAddr),
                APP_ROUTING_OLSR_INRIA,
                ANY_DEST,
                index,
                (char *) msg,
                packetsize,
                IPTOS_PREC_INTERNETCONTROL,
                delay,
                TRACE_OLSR);
        }
    }
}


// /**
// FUNCTION   :: OlsrSend
// LAYER      :: APPLICATION
// PURPOSE    :: Send olsr packet to the UDP layer to specified interface
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + msg : olsrpacket *: OLSR packet to be sent
// + packetsize: Int32: Size of packet
// + jitter : clocktype: jitter to be added to packet
// + interfaceIndex: Int32 : interface to send on
// RETURN :: void : NULL
// **/

static
void OlsrSend(
    Node* node,
    olsrpacket* msg,
    Int32 packetsize,
    clocktype jitter,
    Int32 interfaceIndex)
{
    clocktype delay;
    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;
    Address interfaceAddr;
    interfaceAddr.networkType = NETWORK_IPV4;

        if(olsr->ip_version == NETWORK_IPV6)
        {
            interfaceAddr.networkType = NETWORK_IPV6;
            Ipv6GetGlobalAggrAddress(
                    node,
                    interfaceIndex,
                    &interfaceAddr.interfaceAddr.ipv6);
        }
        else if (olsr->ip_version == NETWORK_IPV4)
        {
            interfaceAddr.networkType = NETWORK_IPV4;
            interfaceAddr.interfaceAddr.ipv4 =
                            NetworkIpGetInterfaceAddress(node,interfaceIndex);
        }
//#endif

    // set msg->seq no with the packet seq no for that interface
    msg->olsr_pack_seq_no = olsr->interfaceSequenceNumbers[interfaceIndex]++;
    delay = (clocktype) (jitter * RANDOM_erand(olsr->seed));


    if (interfaceAddr.networkType == NETWORK_IPV6)
    {
        Address multicastAddr;

        multicastAddr.interfaceAddr.ipv6.s6_addr8[0] = 0xff;
        multicastAddr.interfaceAddr.ipv6.s6_addr8[1] = 0x0e;
        multicastAddr.interfaceAddr.ipv6.s6_addr8[2] = 0x00;
        multicastAddr.interfaceAddr.ipv6.s6_addr8[3] = 0x00;
        multicastAddr.interfaceAddr.ipv6.s6_addr8[4] = 0x00;
        multicastAddr.interfaceAddr.ipv6.s6_addr8[5] = 0x00;
        multicastAddr.interfaceAddr.ipv6.s6_addr8[6] = 0x00;
        multicastAddr.interfaceAddr.ipv6.s6_addr8[7] = 0x00;
        multicastAddr.interfaceAddr.ipv6.s6_addr8[8] = 0x00;
        multicastAddr.interfaceAddr.ipv6.s6_addr8[9] = 0x00;
        multicastAddr.interfaceAddr.ipv6.s6_addr8[10] = 0x00;
        multicastAddr.interfaceAddr.ipv6.s6_addr8[11] = 0x00;
        multicastAddr.interfaceAddr.ipv6.s6_addr8[12] = 0x00;
        multicastAddr.interfaceAddr.ipv6.s6_addr8[13] = 0x00;
        multicastAddr.interfaceAddr.ipv6.s6_addr8[14] = 0x00;
        multicastAddr.interfaceAddr.ipv6.s6_addr8[15] = 0x01;

        multicastAddr.networkType = NETWORK_IPV6;

        APP_UdpSendNewDataWithPriority(
             node,
             APP_ROUTING_OLSR_INRIA,
             interfaceAddr,
             APP_ROUTING_OLSR_INRIA,
             multicastAddr,
             interfaceIndex,
             (char *) msg,
             packetsize,
             IPTOS_PREC_INTERNETCONTROL,
             delay,
             TRACE_OLSR);
    }
    else

    {
        APP_UdpSendNewDataWithPriority(
            node,
            APP_ROUTING_OLSR_INRIA,
            GetIPv4Address(interfaceAddr),
            APP_ROUTING_OLSR_INRIA,
            ANY_DEST,
            interfaceIndex,
            (char *) msg,
            packetsize,
            IPTOS_PREC_INTERNETCONTROL,
            delay,
            TRACE_OLSR);
    }
}


//************************************************************************//
//                MID Message Related Functions                           //
//************************************************************************//

// /**
// FUNCTION   :: OlsrPrintMidMessage
// LAYER      :: APPLICATION
// PURPOSE    :: Print MID msg
// PARAMETERS ::
// + message : mid_message* : MID msg
// RETURN :: void : NULL
// **/
static
void OlsrPrintMidMessage(
    mid_message* message)
{

    char addrString[MAX_STRING_LENGTH];

    IO_ConvertIpAddressToString(&message->mid_origaddr,
        addrString);
    printf("MID Message Content::\n");
    printf("%s [ alias address : ", addrString);

    mid_alias* mid_addr = message->mid_addr;
    while (mid_addr)
    {
        IO_ConvertIpAddressToString(&mid_addr->alias_addr,
            addrString);

        printf("%s ", addrString);

        mid_addr = mid_addr->next;
    }
    printf("]\n");
}


// /**
// FUNCTION   :: OlsrSendMidPacket
// LAYER      :: APPLICATION
// PURPOSE    :: Build MID msg and Send it
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + message : mid_message* : Pointer to a MID msg
// + interfaceIndex : Int32 : Outgoing Interface Index
// RETURN :: void : NULL
// **/
static
void OlsrSendMidPacket(
    Node* node,
    mid_message* message,
    Int32 interfaceIndex)
{
    char packet[MAXPACKETSIZE + 1];
    RoutingOlsr* olsr = (RoutingOlsr*) node->appData.olsr;
    olsrpacket* olsr_pkt = (olsrpacket* )packet;
    olsrmsg* olsr_msg = (olsrmsg* ) olsr_pkt->olsr_msg;
    midmsg* mid_msg = NULL;
    NodeAddress* alias_ipv4_addr = NULL;
    in6_addr* alias_ipv6_addr = NULL;

    if (olsr->ip_version == NETWORK_IPV6)
    {
        mid_msg = olsr_msg->olsr_ipv6_mid;
        alias_ipv6_addr = (in6_addr *)mid_msg->olsr_iface_addr;
    }
    else

    {
        mid_msg = olsr_msg->olsr_ipv4_mid;
        alias_ipv4_addr = (NodeAddress *)mid_msg->olsr_iface_addr;
    }

    mid_alias* mid_addr;
    Int32 outputsize;


    if (!message)
    {
        if (DEBUG)
        {
            printf("OlsrSendMidPacket: NULL msg return.\n");
        }
        return;
    }

    if (DEBUG)
    {
        char addrString[MAX_STRING_LENGTH];
        IO_ConvertIpAddressToString(&message->mid_origaddr,
                addrString);

        char strTime[MAX_STRING_LENGTH];
        ctoa(getSimTime(node), strTime);
        printf("Node %d generates MID message with originator %s"
               " on interface %d at %s\n",
            node->nodeId, addrString, interfaceIndex, strTime);

        OlsrPrintMidMessage(message);
    }

    olsr->olsrStat.numMidGenerated++;

    mid_addr = message->mid_addr;
    while (mid_addr)
    {
        mid_alias* prev_mid_addr;

        if (olsr->ip_version == NETWORK_IPV6)
        {
            *alias_ipv6_addr = GetIPv6Address(mid_addr->alias_addr);
            alias_ipv6_addr++;
        }
        else

        {
            *alias_ipv4_addr = GetIPv4Address(mid_addr->alias_addr);
            alias_ipv4_addr++;
        }
        prev_mid_addr = mid_addr;

        mid_addr = mid_addr->next;

        MEM_free(prev_mid_addr);
    }

    olsr_msg->olsr_vtime = OlsrDouble2ME((Float32)(olsr->mid_hold_time
                                                       / SECOND));
    olsr_msg->olsr_msgtype = MID_PACKET;

    if (olsr->ip_version == NETWORK_IPV6)
    {
        olsr_msg->olsr_msg_tail.olsr_ipv6_msg.msg_seq_no =
            message->mid_seqno;
        olsr_msg->olsr_msg_tail.olsr_ipv6_msg.hop_count =
            message->mid_hopcnt;
        olsr_msg->olsr_msg_tail.olsr_ipv6_msg.ttl = message->mid_ttl;
        outputsize = (Int32)((char *)alias_ipv6_addr - packet);
        olsr_msg->olsr_msg_size = (UInt16) ((char *)alias_ipv6_addr
                                   - (char *)olsr_msg);
        olsr_msg->originator_ipv6_address = GetIPv6Address(
                                                message->mid_origaddr);
    }
    else

    {
        olsr_msg->olsr_msg_tail.olsr_ipv4_msg.msg_seq_no =
            message->mid_seqno;
        olsr_msg->olsr_msg_tail.olsr_ipv4_msg.hop_count =
            message->mid_hopcnt;
        olsr_msg->olsr_msg_tail.olsr_ipv4_msg.ttl = message->mid_ttl;
        outputsize = (Int32)((char *)alias_ipv4_addr - packet);
        olsr_msg->olsr_msg_size = (UInt16) ((char *)alias_ipv4_addr
                                      - (char *)olsr_msg);
        olsr_msg->originator_ipv4_address = GetIPv4Address(
                                                message->mid_origaddr);
    }

   if (DEBUG)
   {
       printf ("Node %d: MID Packet  size is %d\n",
           node->nodeId, outputsize);
   }

    olsr_pkt->olsr_packlen = (UInt16) (outputsize);

    OlsrSend(node,
        olsr_pkt,
        outputsize,
        MAX_MID_JITTER,
        interfaceIndex);

    return;
}


// /**
// FUNCTION   :: OlsrBuildMidPacket
// LAYER      :: APPLICATION
// PURPOSE    :: Build MID Packet
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + message : mid_message* : Pointer to a MID msg
// RETURN :: void : NULL
// **/
static
void OlsrBuildMidPacket(
    Node* node,
    mid_message* message)
{
    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;
    Address main_addr = olsr->main_address;

    message->mid_origaddr = main_addr;  // originator's address
    message->mid_hopcnt = 0;    // number of hops to destination
    message->mid_ttl = MAX_TTL; // ttl

    message->mid_seqno = OlsrGetMsgSeqNo(node);     // sequence number

    message->main_addr = main_addr;     // main address
    message->mid_addr = NULL;  // alias address

    for (Int32 i = 0; i < node->numberInterfaces; i++)
    {
        mid_alias* mid_addr;
        Address interfaceAddr;

        if (NetworkIpGetInterfaceType(node, i) != olsr->ip_version
            && NetworkIpGetInterfaceType(node, i)!= NETWORK_DUAL)
        {
            continue;
        }

        if(olsr->ip_version == NETWORK_IPV6)
        {
            interfaceAddr.networkType = NETWORK_IPV6;
            Ipv6GetGlobalAggrAddress(
                    node,
                    i,
                    &interfaceAddr.interfaceAddr.ipv6);
        }
        else if (olsr->ip_version == NETWORK_IPV4)
        {
            interfaceAddr.networkType = NETWORK_IPV4;
            interfaceAddr.interfaceAddr.ipv4 =
                            NetworkIpGetInterfaceAddress(node,i);
        }
//#endif

        // Do not consider interface with main address and
        // also non-olsr interfaces

        if (Address_IsSameAddress(&interfaceAddr, &main_addr) ||
            (NetworkIpGetUnicastRoutingProtocolType(node, i, olsr->ip_version)
            != ROUTING_PROTOCOL_OLSR_INRIA)
//#endif
            )
        {
            continue;
        }
        mid_addr = (mid_alias* ) MEM_malloc(sizeof(mid_alias));
        memset(mid_addr, 0, sizeof(mid_alias));

        mid_addr->alias_addr = interfaceAddr;
        mid_addr->next = message->mid_addr;
        message->mid_addr = mid_addr;
    }

    return;
}


// /**
// FUNCTION   :: OlsrGenerateMid
// LAYER      :: APPLICATION
// PURPOSE    :: Generate a MID msg
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + interfaceIndex : Int32 : Outgoing Interface Index
// RETURN :: void : NULL
// **/
static
void OlsrGenerateMid(
    Node* node,
    Int32 interfaceIndex)
{
    mid_message midpacket;

    // receive mid packet info from the node structure to mid_message
    OlsrBuildMidPacket(node, &midpacket);

    // prepare the mid message and send
    OlsrSendMidPacket(node, &midpacket, interfaceIndex);

    return;
}


// /**
// FUNCTION   :: OlsrMidForward
// LAYER      :: APPLICATION
// PURPOSE    :: Forward a MID msg
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + m_forward : olsrmsg* : Pointer to a generic olsr msg
// + interfaceIndex : Int32 : Outgoing Interface Index
// RETURN :: void : NULL
// **/
static
void OlsrMidForward(
    Node* node,
    olsrmsg* m_forward)
{

    char packet[MAXPACKETSIZE + 1];
    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;
    olsrpacket* olsr_pkt = (olsrpacket* )packet;
    olsrmsg* olsr_msg = (olsrmsg* ) olsr_pkt->olsr_msg;

    olsr->olsrStat.numMidRelayed++;
    olsr_pkt->olsr_packlen = 2 * sizeof(UInt16) + m_forward->olsr_msg_size;

    memcpy(olsr_msg, m_forward, m_forward->olsr_msg_size);

    OlsrSendonAllInterfaces(node,
        olsr_pkt,
        olsr_pkt->olsr_packlen,
        MAX_MID_JITTER);

    return;
}


// /**
// FUNCTION   :: OlsrMidChgeStruct
// LAYER      :: APPLICATION
// PURPOSE    :: Parse an olsr message and collects all information in MID
//               msg
// PARAMETERS ::
// + node : Node* : Pointer to Node
// + mid_msg : mid_message* : Pointer to MID msg
// + m : olsrmsg* : Pointer to a generic olsr msg
// RETURN :: void : NULL
// **/
static
void OlsrMidChgeStruct(
    Node* node,
    mid_message* mid_msg,
    olsrmsg* m)
{
    midmsg* mid;
    NodeAddress* alias_ipv4_addr = NULL;
    in6_addr* alias_ipv6_addr = NULL;
    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;
    if (!m)
    {
        return;
    }
    if (m->olsr_msgtype != MID_PACKET)
    {
        return;
    }

    // parse olsr message and collects all information in mid_message

    if (olsr->ip_version == NETWORK_IPV6)
    {
        SetIPv6AddressInfo(&mid_msg->mid_origaddr,
            m->originator_ipv6_address);  // originator's address
        SetIPv6AddressInfo(&mid_msg->main_addr, m->originator_ipv6_address);     // main address
        mid = m->olsr_ipv6_mid;
        alias_ipv6_addr = (in6_addr *)mid->olsr_iface_addr;
    }
    else

    {
        SetIPv4AddressInfo(&mid_msg->mid_origaddr,
            m->originator_ipv4_address);  // originator's address
        SetIPv4AddressInfo(&mid_msg->main_addr, m->originator_ipv4_address);     // main address
        mid = m->olsr_ipv4_mid;
        alias_ipv4_addr = (NodeAddress *)mid->olsr_iface_addr;
    }
    mid_msg->vtime = OlsrME2Double(m->olsr_vtime); // validity time
    mid_msg->mid_addr = NULL;  // alias address

    mid_alias* mid_addr;

    if (olsr->ip_version == NETWORK_IPV6)
    {
        // number of hops to destination
        mid_msg->mid_hopcnt = m->olsr_msg_tail.olsr_ipv6_msg.hop_count;
        mid_msg->mid_ttl = MAX_TTL; // ttl
        // sequence number
        mid_msg->mid_seqno = m->olsr_msg_tail.olsr_ipv6_msg.msg_seq_no;
        while ((char *)alias_ipv6_addr < (char *)m + m->olsr_msg_size)
        {
            mid_addr = (mid_alias* )MEM_malloc(sizeof(mid_alias));
            memset(mid_addr, 0, sizeof(mid_alias));

            if (mid_addr == NULL)
            {
                printf("olsrd: out of memery \n");
                break;
            }
            SetIPv6AddressInfo(&mid_addr->alias_addr, *alias_ipv6_addr);
            mid_addr->next = mid_msg->mid_addr;
            mid_msg->mid_addr = mid_addr;
            alias_ipv6_addr++;
        }
    }
    else

    {

        mid_msg->mid_hopcnt = m->olsr_msg_tail.olsr_ipv4_msg.hop_count;
        mid_msg->mid_ttl = MAX_TTL;
        mid_msg->mid_seqno = m->olsr_msg_tail.olsr_ipv4_msg.msg_seq_no;

        while ((char *)alias_ipv4_addr < (char *)m + m->olsr_msg_size)
        {
            mid_addr = (mid_alias* )MEM_malloc(sizeof(mid_alias));
            memset(mid_addr, 0, sizeof(mid_alias));

            if (mid_addr == NULL)
            {
                printf("olsrd: out of memery \n");
                break;
            }
            SetIPv4AddressInfo(&mid_addr->alias_addr, *alias_ipv4_addr);
            mid_addr->next = mid_msg->mid_addr;
            mid_msg->mid_addr = mid_addr;
            alias_ipv4_addr++;
        }
    }
    return;
}

// /**
// FUNCTION   :: OlsrDestroyMidMessage
// LAYER      :: APPLICATION
// PURPOSE    :: Destroy a MID msg
// PARAMETERS ::
// + message : mid_message* : Pointer to MID msg
// RETURN :: void : NULL
// **/
static
void OlsrDestroyMidMessage(
    mid_message* message)
{
    mid_alias* mid_addr = message->mid_addr;

    while (mid_addr)
    {
        mid_alias* prev_mid_addr = mid_addr;
        mid_addr = mid_addr->next;
        MEM_free(prev_mid_addr);
    }

    return;
}

// HNA Message Related Utilities starts

// /**
// FUNCTION   :: OlsrPrintHnaMessage
// LAYER      :: APPLICATION
// PURPOSE    :: print HNA msg
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + message : hna_message* : Pointer to a HNA msg
// RETURN :: void : NULL
// **/

static
void OlsrPrintHnaMessage(Node* node, hna_message* message)
{
    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;
    hna_net_addr* hna_net_pair = message->hna_net_pair;

    printf("HNA Message Content::\n");
    while (hna_net_pair)
    {
        char addrString[MAX_STRING_LENGTH];

        IO_ConvertIpAddressToString(&hna_net_pair->net,
            addrString);
        printf("NonOlsrNetAddress: %s    ", addrString);

        if (olsr->ip_version == NETWORK_IPV6)
        {

            printf("NonOlsrNetPrefixLen: %d\n", hna_net_pair->netmask.v6);

        }
        else
        {
            IO_ConvertIpAddressToString(hna_net_pair->netmask.v4,
                addrString);
            printf("NonOlsrNetMask: %s\n", addrString);

        }

        hna_net_pair = hna_net_pair->next;

    }

    return;
}

// /**
// FUNCTION   :: OlsrDestroyHnaMessage
// LAYER      :: APPLICATION
// PURPOSE    :: destroy HNA msg
// PARAMETERS ::
// + message : hna_message* : Pointer to a HNA msg
// RETURN :: void : NULL
// **/

static
void OlsrDestroyHnaMessage(hna_message* message)
{
    hna_net_addr* hna_net_pair = message->hna_net_pair;

    while (hna_net_pair)
    {
        hna_net_addr* prev_hna_net_pair = hna_net_pair;
        hna_net_pair = hna_net_pair->next;
        MEM_free(prev_hna_net_pair);
    }

    return;
}


// /**
// FUNCTION   :: OlsrSendHnaPacket
// LAYER      :: APPLICATION
// PURPOSE    :: Send HNA Packet
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + message : hna_message* : Pointer to a HNA msg
// + interfaceIndex : Int32 : Outgoing Interface Index
// RETURN :: void : NULL
// **/
static
void OlsrSendHnaPacket(
    Node* node,
    hna_message* message,
    Int32 interfaceIndex)
{
    char packet[MAXPACKETSIZE + 1];
    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;
    olsrpacket* olsr_pkt = (olsrpacket* )packet;
    olsrmsg* olsr_msg = (olsrmsg* ) olsr_pkt->olsr_msg;
    hnamsg* hna_msg = NULL;
    struct _hnapair_ipv6* hnapair_ipv6 = NULL;
    struct _hnapair_ipv4* hnapair_ipv4 = NULL;


    if (olsr->ip_version == NETWORK_IPV6)
    {
        hna_msg = olsr_msg->olsr_ipv6_hna;
        hnapair_ipv6 = (struct _hnapair_ipv6* )hna_msg->hna_net_pair;
    }
    else

    {
        hna_msg = olsr_msg->olsr_ipv4_hna;
        hnapair_ipv4 = (struct _hnapair_ipv4* )hna_msg->hna_net_pair;
    }


    if (!message)
    {
          if (DEBUG)
        {
            printf("OlsrSendHnaPacket: NULL msg return.\n");
        }
        return;
    }

    olsr->olsrStat.numHnaGenerated++;

    hna_net_addr* hna_net_pair = message->hna_net_pair;

    while (hna_net_pair)
    {

        if (olsr->ip_version == NETWORK_IPV6)
        {
            hnapair_ipv6->addr = GetIPv6Address(hna_net_pair->net);

            hnapair_ipv6->netmask.s6_addr32[3] = hna_net_pair->netmask.v6;

            hnapair_ipv6++;
        }
        else

        {
            hnapair_ipv4->addr = GetIPv4Address(hna_net_pair->net);

            hnapair_ipv4->netmask = hna_net_pair->netmask.v4;

            hnapair_ipv4++;
        }

        hna_net_pair = hna_net_pair->next;
    }

    olsr_msg->olsr_vtime = OlsrDouble2ME((Float32)(olsr->hna_hold_time
                                                       / SECOND));
    olsr_msg->olsr_msgtype = HNA_PACKET;

    if (olsr->ip_version == NETWORK_IPV6)
    {
        olsr_msg->olsr_msg_size = UInt16((char *)hnapair_ipv6 -
                                                           (char *)olsr_msg);
        olsr_pkt->olsr_packlen = UInt16((char *)hnapair_ipv6 -
                                                             (char *)packet);
        olsr_msg->olsr_msg_tail.olsr_ipv6_msg.msg_seq_no =
            message->hna_seqno;
        olsr_msg->olsr_msg_tail.olsr_ipv6_msg.ttl = message->hna_ttl;
        olsr_msg->olsr_msg_tail.olsr_ipv6_msg.hop_count =
            message->hna_hopcnt;
        olsr_msg->originator_ipv6_address = GetIPv6Address(
                                                message->hna_origaddr);
    }
    else
    {
        olsr_msg->olsr_msg_size = UInt16((char *)hnapair_ipv4 -
                                                           (char *)olsr_msg);
        olsr_pkt->olsr_packlen = UInt16((char *)hnapair_ipv4 -
                                                             (char *)packet);
        olsr_msg->olsr_msg_tail.olsr_ipv4_msg.msg_seq_no =
            message->hna_seqno;
        olsr_msg->olsr_msg_tail.olsr_ipv4_msg.ttl = message->hna_ttl;
        olsr_msg->olsr_msg_tail.olsr_ipv4_msg.hop_count =
            message->hna_hopcnt;
        olsr_msg->originator_ipv4_address = GetIPv4Address(
                                                message->hna_origaddr);
    }

    if (DEBUG)
    {
        OlsrPrintHnaMessage(node, message);
    }

    OlsrSend(node,
        olsr_pkt,
        olsr_pkt->olsr_packlen,
        MAX_HNA_JITTER,
        interfaceIndex);

    OlsrDestroyHnaMessage(message);

    return;
}

// /**
// FUNCTION   :: OlsrBuildHnaPacket
// LAYER      :: APPLICATION
// PURPOSE    :: Build HNA pkt
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + message : hna_message* : Pointer to a HNA msg
// RETURN :: void : NULL
// **/

static
void OlsrBuildHnaPacket(
    Node* node,
    hna_message* message)
{
    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    message->hna_origaddr = olsr->main_address; // originator
    message->hna_hopcnt = 0;     // number of hops to destination
    message->hna_ttl = MAX_TTL;  // ttl

    message->hna_seqno = OlsrGetMsgSeqNo(node); // sequence number
    message->hna_net_pair = NULL;

    // Add non-olsr network address and netmask to the msg-tail
    // i.e. link list of message->hna_net_pair

    for (Int32 i = 0; i < node->numberInterfaces; i++)
    {
        if (NetworkIpGetUnicastRoutingProtocolType(node, i, olsr->ip_version)
            != ROUTING_PROTOCOL_OLSR_INRIA
            && NetworkIpInterfaceIsEnabled(node, i)
            )
        {

            Address netAddr;
            NetworkGetInterfaceInfo(node, i, &netAddr, olsr->ip_version);


        if (olsr->ip_version != netAddr.networkType)
        {
            continue;
        }
        hna_net_addr* hna_net_pair = (hna_net_addr*) MEM_malloc(
                                                       sizeof(hna_net_addr));
        memset(hna_net_pair, 0, sizeof(hna_net_addr));
//#endif

            if (olsr->ip_version == NETWORK_IPV6)
            {
                hna_net_pair->netmask.v6 = MAX_PREFIX_LEN;

                Ipv6GetPrefix(&netAddr.interfaceAddr.ipv6,
                    &hna_net_pair->net.interfaceAddr.ipv6,
                    hna_net_pair->netmask.v6);
                hna_net_pair->net.networkType = NETWORK_IPV6;

            }
            else
            {
                hna_net_pair->netmask.v4 =
                        NetworkIpGetInterfaceSubnetMask(node, i);

                if (hna_net_pair->netmask.v4)
                {
                    hna_net_pair->net.interfaceAddr.ipv4 =
                       netAddr.interfaceAddr.ipv4 & hna_net_pair->netmask.v4;
                }
                else
                {
                    hna_net_pair->net.interfaceAddr.ipv4 =
                                                  netAddr.interfaceAddr.ipv4;
                }
                hna_net_pair->net.networkType = NETWORK_IPV4;
            }
            hna_net_pair->next = message->hna_net_pair;
            message->hna_net_pair = hna_net_pair;
        }
    }
    return;
}


// /**
// FUNCTION   :: OlsrGenerateHna
// LAYER      :: APPLICATION
// PURPOSE    :: Builds and sends a HNA message
// PARAMETERS ::
//               :Pointer to Node structure
//               : Outgoing Interface Index
// RETURN :: void : NULL
// **/

static
void OlsrGenerateHna(
    Node* node,
    Int32 interfaceIndex)
{
    hna_message hnapacket;

    OlsrBuildHnaPacket(node, &hnapacket);
    OlsrSendHnaPacket(node, &hnapacket, interfaceIndex);

    return;

}
/***************************************************************************
 *                   Definition of Topology Table                          *
 ***************************************************************************/
/*
//Peter added for combine...
static
void OlsrDeleteCombinedListofLast(
						  topology_last_entry* last_entry,
						  Address dst)
{
	destination_list* dest_list;
	destination_list* dest_list_tmp;

	ERROR_Assert(last_entry, "Invalid topology entry");

	// get destination list from this topology
	dest_list = last_entry->topology_list_of_destinations;
	last_entry->topology_list_of_destinations = NULL;

	while (dest_list != NULL)
	{
		if (Address_IsSameAddress(&dest_list->destination_node->
			topology_destination_dst, &dst))
		{
			// address matches, remove from the destination list
			dest_list_tmp = dest_list;
			dest_list = dest_list->next;
			MEM_free(dest_list_tmp);
		}
		else
		{
			dest_list_tmp = dest_list;
			dest_list = dest_list->next;
			dest_list_tmp->next = last_entry->topology_list_of_destinations;
			last_entry->topology_list_of_destinations = dest_list_tmp;
		}
	}
}
*/

// /**
// FUNCTION   :: OlsrDeleteListofLast
// LAYER      :: APPLICATION
// PURPOSE    :: Deletes address from destination list of current
//               topology entries
// PARAMETERS ::
// + last_entry : topology_last_entry* : Pointer to Topology entry list
// + dst : Address: Address to be deleted
// RETURN :: void : NULL
// **/

static
void OlsrDeleteListofLast(
    topology_last_entry* last_entry,
    Address dst)
{
    destination_list* dest_list;
    destination_list* dest_list_tmp;

    ERROR_Assert(last_entry, "Invalid topology entry");

    // get destination list from this topology
    dest_list = last_entry->topology_list_of_destinations;
    last_entry->topology_list_of_destinations = NULL;

    while (dest_list != NULL)
    {
        if (Address_IsSameAddress(&dest_list->destination_node->
                topology_destination_dst, &dst))
        {
            // address matches, remove from the destination list			
            dest_list_tmp = dest_list;
            dest_list = dest_list->next;
            MEM_free(dest_list_tmp);
        }
        else
        {
            dest_list_tmp = dest_list;
            dest_list = dest_list->next;
            dest_list_tmp->next = last_entry->topology_list_of_destinations;
            last_entry->topology_list_of_destinations = dest_list_tmp;
        }
    }
}


// /**
// FUNCTION   :: OlsrDeleteDestTopolgyTable
// LAYER      :: APPLICATION
// PURPOSE    :: Deletes destination list from topology table
// PARAMETERS ::
// + dest_entry : topology_destination_entry * : Pointer to destination list
// RETURN :: void : NULL
// **/

static
void OlsrDeleteDestTopolgyTable(
    topology_destination_entry* dest_entry)
{
    last_list* list_of_last;
    topology_last_entry* last_entry;

    ERROR_Assert(dest_entry, "Invalid topology entry");

    list_of_last = dest_entry->topology_destination_list_of_last;

    while (list_of_last != NULL)
    {
        last_entry = list_of_last->last_neighbor;

        OlsrDeleteListofLast(last_entry,
                                 dest_entry->topology_destination_dst);

        dest_entry->topology_destination_list_of_last = list_of_last->next;
        MEM_free(list_of_last);
        list_of_last = dest_entry->topology_destination_list_of_last;
    }
    OlsrRemoveList((olsr_qelem* ) dest_entry);
    MEM_free((void* ) dest_entry);
}

//Peter added for combine...
static
void OlsrDeleteCombinedDestTopolgyTable(
								topology_destination_entry* dest_entry)
{
	last_list* list_of_last;
	topology_last_entry* last_entry;

	ERROR_Assert(dest_entry, "Invalid topology entry");

	//dest_entry->topology_destination_list_of_last = NULL;
	
	list_of_last = dest_entry->topology_destination_list_of_last;

	while (list_of_last != NULL)
	{
		last_entry = list_of_last->last_neighbor;
		
		/*
		OlsrDeleteCombinedListofLast(last_entry,
			dest_entry->topology_destination_dst);
		*/
		//last_entry->topology_last;
		MEM_free(last_entry);		

		dest_entry->topology_destination_list_of_last = list_of_last->next;
		MEM_free(list_of_last);
		list_of_last = dest_entry->topology_destination_list_of_last;
	}
	

	OlsrRemoveList((olsr_qelem* ) dest_entry);
	MEM_free((void* ) dest_entry);
}

// /**
// FUNCTION   :: OlsrDeleteListofDest
// LAYER      :: APPLICATION
// PURPOSE    :: Deletes address from destination list
// PARAMETERS ::
// + dest_entry : topology_destination_entry*  : Pointer to Topology
//                                               destination list
// + dst : Address: Address to be deleted
// RETURN :: void : NULL
// **/

static
void OlsrDeleteListofDest(
    topology_destination_entry* dest_entry,
    Address dst)
{
    last_list *list_of_last;
    last_list *list_of_last_tmp;

    ERROR_Assert(dest_entry, "Invalid topology entry");

    list_of_last = dest_entry->topology_destination_list_of_last;
    dest_entry->topology_destination_list_of_last = NULL;

    while (list_of_last != NULL)
    {
        if (Address_IsSameAddress(&list_of_last->last_neighbor->
                topology_last, &dst))
        {
            list_of_last_tmp = list_of_last;
            list_of_last = list_of_last->next;
            MEM_free(list_of_last_tmp);
        }
        else
        {
            list_of_last_tmp = list_of_last;
            list_of_last = list_of_last->next;
            list_of_last_tmp->next =
                    dest_entry->topology_destination_list_of_last;

            dest_entry->topology_destination_list_of_last = list_of_last_tmp;
        }
    }

    if (dest_entry->topology_destination_list_of_last == NULL)
    {
        OlsrRemoveList((olsr_qelem *)dest_entry);
        MEM_free((void *)dest_entry);
    }
}


//SYMMETRIC TOPOLOGY TABLE

//this function will only be called by OlsrReleaseTopologyTableSYM,
//although OlsrReleaseTopologyTableSYM is never called
static
void OlsrDeleteLastTopolgyTableSYMInSerial(topology_last_entry* last_entry)
{

	destination_list* list_of_dest;
	topology_destination_entry* dest_entry;

	ERROR_Assert(last_entry, "Invalid topology entry");

	list_of_dest = last_entry->topology_list_of_destinations;

	while (list_of_dest != NULL)
	{
		dest_entry = list_of_dest->destination_node;

		//The only change is here, compared to OlsrDeleteLastTopolgyTable
		//OlsrDeleteListofDest(dest_entry, last_entry->topology_last);
		MEM_free(dest_entry);
		
		
		last_entry->topology_list_of_destinations = list_of_dest->next;
		MEM_free(list_of_dest);
		list_of_dest = last_entry->topology_list_of_destinations;
	}

	OlsrRemoveList((olsr_qelem *)last_entry);
	MEM_free((void *)last_entry);

}

static
bool OlsrDeleteLastTopolgyTableSYM(Node* node,
								topology_last_entry* last_entry, BOOL bDeleteSYM = TRUE)
{


	//printf("OlsrDeleteLastTopolgyTableSYM begin \n");

	bool bDeleteAll = false;
	/*
	//if (node->nodeId == 2)
	{
		//DebugBreak();
	}
	*/
	
	RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

	destination_list* list_of_dest;
	topology_destination_entry* dest_entry;

	ERROR_Assert(last_entry, "Invalid topology entry");

	list_of_dest = last_entry->topology_list_of_destinations;


	if (g_iSymmetricDifferentCode == 1)
	//if (g_iSymmetricDifferentCode == 1 && bDeleteSYM)
	{
	
		////////////////////////////////////////////////////////////////////////
		//for symmetric, first delete the dests of the last entries that similar as the dest nodes of this last entry
		
		destination_list* list_of_dest_tmp = last_entry->topology_list_of_destinations;
		
		while (list_of_dest_tmp != NULL)
		{
			topology_destination_entry* dest_entry_tmp = list_of_dest_tmp->destination_node;

			//if (dest_entry_tmp->topology_destination_info.bAddForNormal)
			{

				topology_last_entry * t_last_sym = OlsrLookupLastTopologyTableSYM(node, dest_entry_tmp->topology_destination_dst);

				if (t_last_sym != NULL) 
				{
					//BOOL bEmpty = TRUE;

					destination_list* topo_dest_sym = OlsrinListDestTopology(t_last_sym, last_entry->topology_last);


					if (topo_dest_sym != NULL)
					{
						topology_destination_entry* dest_node_tmp = topo_dest_sym->destination_node;


						// Peter comment, uncertain whether need to force delete the "symetric" one even if it was added in a "normal" way,
						// just keep it.
						
						//Peter comment: now try to delete anyway
						//if (dest_node_tmp->topology_destination_info.bAddForSymmetric)
						{

							dest_node_tmp->topology_destination_info.bAddForSymmetric = FALSE;

							//Peter comment: now try to delete anyway
							//if (!dest_node_tmp->topology_destination_info.bAddForSymmetric && !dest_node_tmp->topology_destination_info.bAddForNormal)
							{

								OlsrDeleteListofLast(t_last_sym, last_entry->topology_last);

								if (dest_node_tmp != NULL)
								{
									MEM_free(dest_node_tmp);
									dest_node_tmp = NULL;
								}

								//if the last entry become empty after delete the specific dest node
								
								//Peter ######??????????%%%%%%%%%%% still require further study
								//if (t_last_sym->topology_list_of_destinations == NULL)
								if (t_last_sym->topology_list_of_destinations == NULL  && bDeleteSYM)
								{
									OlsrRemoveList((olsr_qelem *)t_last_sym);
									MEM_free((void *)t_last_sym);
								}
							}							
						}
					}
					else
					{

						//this branch should not exist because of the symmetric property
						//currently just comment it
						//printf("!!!!!!!!!!!! this branch should not exist because of the symmetric property in OlsrDeleteLastTopolgyTableSYM 1 \n");

						//DebugBreak();
					}

				}
				else
				{
					//this branch should not exist because of the symmetric property
					printf("!!!!!!!!!!!! this branch should not exist because of the symmetric property in OlsrDeleteLastTopolgyTableSYM 2 \n");

				}
			}
			
			 
			list_of_dest_tmp = list_of_dest_tmp->next;
		}


		////////////////////////////////////////////////////////////////////
	}
	
	while (list_of_dest != NULL)
	{
		dest_entry = list_of_dest->destination_node;

		//OlsrDeleteListofDest(dest_entry, last_entry->topology_last);

		insert_into_tco_node_addr_set(&(olsr->recent_delete_list), GetIPv4Address(dest_entry->topology_destination_dst));

		MEM_free(dest_entry);

		last_entry->topology_list_of_destinations = list_of_dest->next;
		MEM_free(list_of_dest);

		list_of_dest = last_entry->topology_list_of_destinations;
	}
	

	/*
	while (list_of_dest != NULL)
	{
		dest_entry = list_of_dest->destination_node;
		list_of_dest = list_of_dest->next;

		//if (dest_entry->topology_destination_info.bAddForNormal)
		{
			dest_entry->topology_destination_info.bAddForNormal = FALSE;

			//Peter comment: now try to delete anyway
			//After comment the following line, that would be bug
			
			//if (!dest_entry->topology_destination_info.bAddForNormal && !dest_entry->topology_destination_info.bAddForSymmetric)
			{


				//DebugBreak();

				insert_into_tco_node_addr_set(&(olsr->recent_delete_list), GetIPv4Address(dest_entry->topology_destination_dst));
				//insert_into_tco_node_addr_set(&(olsr->recent_delete_list), GetIPv4Address(dest_entry->topology_destination_dst)+1);
				//insert_into_tco_node_addr_set(&(olsr->recent_delete_list), GetIPv4Address(dest_entry->topology_destination_dst)+2);
				
				
				//do not need, since we do create new but do not add the dest to table
				//OlsrDeleteListofDest(dest_entry, last_entry->topology_last);

				OlsrDeleteListofLast(last_entry, dest_entry->topology_destination_dst);
				
				//last_entry->topology_list_of_destinations = list_of_dest->next;
				//MEM_free(list_of_dest);
				//list_of_dest = last_entry->topology_list_of_destinations;
				

				MEM_free(dest_entry);

			}

		}
		//else
		{
			
		}		
		
	}
	*/


	if (last_entry->topology_list_of_destinations == NULL)
	{

		OlsrRemoveList((olsr_qelem *)last_entry);
		MEM_free((void *)last_entry);

		//last_entry = NULL;
		bDeleteAll = true;

	}


	//printf("OlsrDeleteLastTopolgyTableSYM end \n");


	return bDeleteAll;

}



// /**
// FUNCTION   :: OlsrDeleteLastTopolgyTable
// LAYER      :: APPLICATION
// PURPOSE    :: Deletes last entry from topology table
// PARAMETERS ::
// + last_entry : topology_last_entry* : Pointer to last entry
// RETURN :: void : NULL
// **/

static
void OlsrDeleteLastTopolgyTable(
    topology_last_entry* last_entry)
{
    destination_list* list_of_dest;
    topology_destination_entry* dest_entry;

    ERROR_Assert(last_entry, "Invalid topology entry");

    list_of_dest = last_entry->topology_list_of_destinations;

    while (list_of_dest != NULL)
    {
        dest_entry = list_of_dest->destination_node;

        OlsrDeleteListofDest(dest_entry, last_entry->topology_last);
        last_entry->topology_list_of_destinations = list_of_dest->next;
        MEM_free(list_of_dest);
        list_of_dest = last_entry->topology_list_of_destinations;
    }

    OlsrRemoveList((olsr_qelem *)last_entry);
    MEM_free((void *)last_entry);
}


//SYMMETRIC TOPOLOGY TABLE

static
void OlsrInsertLastTopologyTableSYM(
								 Node* node,
								 //topology_last_entry* last_entry,
								 tc_message* message)
{

	// We must insert new entries contained in received message
	topology_last_entry * t_last_sym = (topology_last_entry *)
		MEM_malloc(sizeof(topology_last_entry));

	memset(t_last_sym, 0, sizeof(topology_last_entry));


	UInt32 hash;
	topology_last_hash* top_last_hash;

	RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

	ERROR_Assert(t_last_sym, "Invalid topology entry");
	ERROR_Assert(message, "Invalid TC message");

	OlsrHashing(message->originator, &hash);
	top_last_hash = &olsr->sym_topologylasttable[hash % HASHMASK];

	/* prepare the last entry */
	t_last_sym->topology_last = message->originator;
	t_last_sym->topology_list_of_destinations = NULL;
	t_last_sym->topologylast_hash = hash;
	t_last_sym->topology_seq = message->ansn;

	t_last_sym->topology_timer = getSimTime(node)
		+ (clocktype)(message->vtime * SECOND);

	OlsrInsertList((olsr_qelem *)t_last_sym, (olsr_qelem *)top_last_hash);
}



// /**
// FUNCTION   :: OlsrInsertLastTopologyTable
// LAYER      :: APPLICATION
// PURPOSE    :: Inserts the originator message from TC message in last entry
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + last_entry : topology_last_entry* : Pointer to topology last entry
// + message : tc_message* : Pointer to tc message
// RETURN :: void : NULL
// **/

static
void OlsrInsertLastTopologyTable(
    Node* node,
    topology_last_entry* last_entry,
    tc_message* message, BOOL bApplyForSymmetricAsWell = FALSE)
{

	//printf("OlsrInsertLastTopologyTable Begin \n");

	UInt32 hash;
	topology_last_hash* top_last_hash;

	RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

	ERROR_Assert(last_entry, "Invalid topology entry");
	ERROR_Assert(message, "Invalid TC message");

	OlsrHashing(message->originator, &hash);
	top_last_hash = &olsr->topologylasttable[hash % HASHMASK];

	/* prepare the last entry */
	last_entry->topology_last = message->originator;
	last_entry->topology_list_of_destinations = NULL;
	last_entry->topologylast_hash = hash;
	last_entry->topology_seq = message->ansn;

	last_entry->topology_timer = getSimTime(node)
		+ (clocktype)(message->vtime * SECOND);

	OlsrInsertList((olsr_qelem *)last_entry, (olsr_qelem *)top_last_hash);

	if (SYMMETRIC_TOPOLOGY_TABLE && bApplyForSymmetricAsWell)
	{
		OlsrInsertLastTopologyTableSYM(node, 
									//last_entry, 
									message);
	}


	//printf("OlsrInsertLastTopologyTable End \n");

}

// /**
// FUNCTION   :: OlsrInsertDestTopologyTable
// LAYER      :: APPLICATION
// PURPOSE    :: Inserts the MPR address from the TC message in dest entry
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + dest_entry : topology_destination_entry* : Pointer to Topology
//                                               destination  entry
// + mpr : tc_mpr_addr* : pointer to mpr address to be added
// RETURN :: void : NULL
// **/

static
void OlsrInsertDestTopologyTable(
    Node* node,
    topology_destination_entry* dest_entry,
    tc_mpr_addr* mpr)
{
    UInt32 hash;
    topology_destination_hash* top_dest_hash;

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    ERROR_Assert(dest_entry, "Invalid topology entry");
    ERROR_Assert(mpr, "Invalid MPR entry");

    OlsrHashing(mpr->address, &hash);

    top_dest_hash = &olsr->topologytable[hash % HASHMASK];

    dest_entry->topology_destination_dst = mpr->address;
    dest_entry->topology_destination_list_of_last = NULL;
    dest_entry->topologydestination_hash = hash;

    OlsrInsertList((olsr_qelem* )dest_entry, (olsr_qelem *)top_dest_hash);
}


static
void OlsrInsertCombinedTopologyTable(
								 Node* node,
								 topology_destination_entry* dest_entry,
								 Address addr)
{
	UInt32 hash;
	topology_destination_hash* top_dest_hash;

	RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

	ERROR_Assert(dest_entry, "Invalid topology entry");
	
	//SetIPv4AddressInfo(&dest_entry->topology_destination_dst, addr);
	
	OlsrHashing(addr, &hash);

	top_dest_hash = &olsr->combined_topologytable[hash % HASHMASK];	

	dest_entry->topology_destination_dst = addr;
	dest_entry->topology_destination_list_of_last = NULL;
	dest_entry->topologydestination_hash = hash;

	OlsrInsertList((olsr_qelem* )dest_entry, (olsr_qelem *)top_dest_hash);
}


//SYMMETRIC TOPOLOGY TABLE

static
topology_last_entry* OlsrLookupLastTopologyTableSYM(
	Node* node,
	Address last)
{
	topology_last_entry* top_last;
	topology_last_hash* top_last_hash;
	UInt32 hash;

	RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

	OlsrHashing(last, &hash);

	top_last_hash = &olsr->sym_topologylasttable[hash % HASHMASK];

	for (top_last = top_last_hash->topology_last_forw;
		top_last != (topology_last_entry* ) top_last_hash;
		top_last = top_last->topology_last_forw)
	{
		if (top_last->topologylast_hash != hash)
		{
			continue;
		}

		// address matches with the topology last address?
		if (Address_IsSameAddress(&top_last->topology_last, &last))
		{
			return top_last;
		}
	}
	return NULL;
}


// /**
// FUNCTION   :: OlsrLookupLastTopologyTable
// LAYER      :: APPLICATION
// PURPOSE    :: Searches the address in the last entry
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + last : Address :  address to be searched
// RETURN :: topology_last_entry* : Pointer to entry if found.
//                                   else NULL
// **/

static
topology_last_entry* OlsrLookupLastTopologyTable(
    Node* node,
    Address last)
{


	topology_last_entry* top_last;
	topology_last_hash* top_last_hash;
	UInt32 hash;

	RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

	OlsrHashing(last, &hash);

	top_last_hash = &olsr->topologylasttable[hash % HASHMASK];

	for (top_last = top_last_hash->topology_last_forw;
		top_last != (topology_last_entry* ) top_last_hash;
		top_last = top_last->topology_last_forw)
	{
		if (top_last->topologylast_hash != hash)
		{
			continue;
		}

		// address matches with the topology last address?
		if (Address_IsSameAddress(&top_last->topology_last, &last))
		{
			return top_last;
		}
	}
	return NULL;   
}

// /**
// FUNCTION   :: OlsrLookupDestTopologyTable
// LAYER      :: APPLICATION
// PURPOSE    :: Searches the address in the dest entry
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + dest : Address : Address to be searched
// RETURN :: topology_dest_entry* : Pointer to entry if found.
//                                   else NULL
// **/

static
topology_destination_entry* OlsrLookupDestTopologyTable(
    Node* node,
    Address dest)
{
    topology_destination_entry* top_dest;
    topology_destination_hash* top_dest_hash;
    UInt32 hash;

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    if (DEBUG)
    {
        printf("OlsrLookupDestTopologyTable\n");
    }

    OlsrHashing(dest, &hash);

    top_dest_hash = &olsr->topologytable[hash % HASHMASK];

    for (top_dest = top_dest_hash->topology_destination_forw;
        top_dest != (topology_destination_entry* ) top_dest_hash;
        top_dest = top_dest->topology_destination_forw)
    {
        if (top_dest->topologydestination_hash != hash)
        {
            continue;
        }

        // matches the address with anyone from destination list
        if(Address_IsSameAddress(&top_dest->topology_destination_dst, &dest))
        {
            return top_dest;
        }
    }
    return NULL;
}

//Peter added for combine...
static
topology_destination_entry* OlsrLookupCombinedTopologyTable(
	Node* node,
	Address dest)
{
	topology_destination_entry* top_dest;
	topology_destination_hash* top_dest_hash;
	UInt32 hash;

	RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

	if (DEBUG)
	{
		printf("OlsrLookupCombinedTopologyTable\n");
	}

	OlsrHashing(dest, &hash);

	top_dest_hash = &olsr->combined_topologytable[hash % HASHMASK];

	for (top_dest = top_dest_hash->topology_destination_forw;
		top_dest != (topology_destination_entry* ) top_dest_hash;
		top_dest = top_dest->topology_destination_forw)
	{
		if (top_dest->topologydestination_hash != hash)
		{
			continue;
		}

		// matches the address with anyone from destination list
		if(Address_IsSameAddress(&top_dest->topology_destination_dst, &dest))
		{
			return top_dest;
		}
	}
	return NULL;
}


// /**
// FUNCTION   :: OlsrinListDestTopology
// LAYER      :: APPLICATION
// PURPOSE    :: Searches the address in the dest entry of this last entry
// PARAMETERS ::
// + last_entry : topology_last_entry* : Pointer to Topology
//                                               last  entry
// + address : Address : Address to be searched
// RETURN :: destination_list* : Pointer to destination list if found,
//                                else NULL
// **/


static
destination_list* OlsrinListDestTopology(
    topology_last_entry* last_entry,
    Address address)
{
    destination_list* list_of_dest;

    ERROR_Assert(last_entry, "Invalid topology entry");

    list_of_dest = last_entry->topology_list_of_destinations;

    if (DEBUG)
    {
        printf("OlsrinListDestTopology\n");
    }

    while (list_of_dest != NULL)
    {
        if (Address_IsSameAddress(
                &list_of_dest->destination_node->topology_destination_dst,
                &address))
        {
            // matches return list of destination
            return list_of_dest;
        }
        list_of_dest = list_of_dest->next;
    }
    return NULL;
}

//Peter Added for combine...
static
last_list* OlsrinListLastTopology(
	last_list* list_of_last,
	Address address)
{
	//last_list* list_of_dest;

	//ERROR_Assert(last_entry, "Invalid topology entry");

	

	while (list_of_last != NULL)
	{
	
		if (Address_IsSameAddress(
			&list_of_last->last_neighbor->topology_last,
			&address))
		{
			// matches return list of last
			return list_of_last;
		}
		list_of_last = list_of_last->next;
	}
	return NULL;
}

// /**
// FUNCTION   :: OlsrUpdateLastTable
// LAYER      :: APPLICATION
// PURPOSE    :: This function updates time out for the
//               existing last entry and
//               creates new entries for the new destinations
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + last_entry : topology_last_entry * : entry to be updated
// + message : tc_message* : Pointer to tc msg
// + addr_ip : Address : address to be updated
// RETURN :: void : NULL
// **/

static
void OlsrUpdateLastTable(
    Node* node,
    topology_last_entry* last_entry,
    tc_message* message,
    Address addr_ip, BOOL bFurtherDetermine = FALSE)
{
     // This function updates time out for the existant pointed by t_last and
     // creates new entries for the new destinations
	/*
	if (node->nodeId == 0)
	{
		g_iTopologyTableUpdateCount++;
	}
	*/
	
	//printf("OlsrUpdateLastTable Begin \n");

    tc_mpr_addr* mpr;
    destination_list* topo_dest;
    topology_destination_entry* destination_entry;
    last_list* topo_last;

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    ERROR_Assert(last_entry, "Invalid topology entry");
    ERROR_Assert(message, "Invalid TC message");

    mpr = message->multipoint_relay_selector_address;

    // refresh timer
    last_entry->topology_timer = getSimTime(node)
                                 + (clocktype)(message->vtime * SECOND);

	topology_last_entry* last_entry_for_sym = NULL;

	if (SYMMETRIC_TOPOLOGY_TABLE)
	{
		last_entry_for_sym = OlsrLookupLastTopologyTableSYM(node, message->originator);
		if (last_entry_for_sym != NULL)
		{

			// refresh timer
			last_entry_for_sym->topology_timer = getSimTime(node)
				+ (clocktype)(message->vtime * SECOND);
		}
		else
		{
			printf("!!!!!!!!!!!! this branch should not exist because of the symmetric property in in OlsrUpdateLastTable 4 \n");
		}
	}
		
	

    if (DEBUG)
    {
        printf("Updating this top_last !\n");
        printf("The list of MPRs is\n:");
        while (mpr != NULL)
        {
            char addrString[MAX_STRING_LENGTH];
            IO_ConvertIpAddressToString(&mpr->address,
                                        addrString);

            printf("This mpr is %s\n", addrString);
            mpr = mpr->next;
        }
        mpr = message->multipoint_relay_selector_address;
    }

    // search in the MPR list of TC message
    while (mpr != NULL)
    {
        // this node ip address in the MPR list not considered
        if (!Address_IsSameAddress(&mpr->address, &addr_ip))
        {
            if ((topo_dest = OlsrinListDestTopology(
                last_entry, mpr->address)) == NULL)
            {
                // if not in the topology table
                if (DEBUG)
                {
                    printf("update last table\n");
                }

				if (bFurtherDetermine)
				{
					bFurtherDetermine = FALSE;
					
					olsr->bAddNew = TRUE;
					
					g_iTopologyChgByOlsrUpdateLastTable++;

					if (!SYMMETRIC_TOPOLOGY_TABLE)
					{
						olsr->changes_topology = TRUE;
					}
				}

                //so need to add this dest to the last-entry of the last_topology table, 
				//since it is not yet in 
		
                

                // search in the destination list
                if ((destination_entry = OlsrLookupDestTopologyTable
                    (node, mpr->address)) == NULL)
                {
                    // not found, insert in the destination list
                    destination_entry = (topology_destination_entry *)
                        MEM_malloc(sizeof(topology_destination_entry));

                    memset(
                        destination_entry,
                        0,
                        sizeof(topology_destination_entry));

                    OlsrInsertDestTopologyTable(node,
                            destination_entry, mpr);
                }

                // creating the structure for the linkage
                topo_dest = (destination_list *)
                        MEM_malloc(sizeof(destination_list));
                memset(topo_dest, 0, sizeof(destination_list));

                topo_dest->next = last_entry->topology_list_of_destinations;
                last_entry->topology_list_of_destinations = topo_dest;

                topo_last = (last_list *) MEM_malloc(sizeof(last_list));
                memset(topo_last, 0, sizeof(last_list));

                topo_last->next =
                    destination_entry->topology_destination_list_of_last;

                destination_entry->topology_destination_list_of_last =
                    topo_last;

                // linking the last and the dest
                topo_last->last_neighbor = last_entry;
                topo_dest->destination_node = destination_entry;


            }



			if (SYMMETRIC_TOPOLOGY_TABLE)
			{

				//olsr->changes_topology = TRUE;
				
				/*
				if (node->nodeId == 1)
				{
				DebugBreak();
				}
				*/

				destination_list* topo_dest_for_sym;

				if (last_entry_for_sym != NULL)
				{

					//this branch may certainly happen 
					//since sym_topologylasttable can be considered as a mirror of the topologylasttable

					topo_dest_for_sym = OlsrinListDestTopology(last_entry_for_sym, mpr->address);
					if (topo_dest_for_sym == NULL)
					{

						//this branch may certainly happen 
						//since sym_topologylasttable can be considered as a mirror of the topologylasttable

						// creating the structure for the linkage
						topo_dest_for_sym = (destination_list *)
							MEM_malloc(sizeof(destination_list));
						memset(topo_dest_for_sym, 0, sizeof(destination_list));


						topo_dest_for_sym->next = last_entry_for_sym->topology_list_of_destinations;
						last_entry_for_sym->topology_list_of_destinations = topo_dest_for_sym;

						//Peter comment: we need the dest_entry, but do not need its last_list anymore
						topology_destination_entry * destination_entry_for_sym = (topology_destination_entry *)
							MEM_malloc(sizeof(topology_destination_entry));

						memset(destination_entry_for_sym, 0, sizeof(topology_destination_entry));

						destination_entry_for_sym->topology_destination_dst = mpr->address;
						destination_entry_for_sym->topology_destination_list_of_last = NULL;
						
						destination_entry_for_sym->topology_destination_info.bAddForNormal = TRUE;


						UInt32 hash_for_sym;

						OlsrHashing(mpr->address, &hash_for_sym);

						destination_entry_for_sym->topologydestination_hash = hash_for_sym;

						topo_dest_for_sym->destination_node = destination_entry_for_sym;


						if (remove_from_tco_node_addr_set(&(olsr->recent_delete_list), GetIPv4Address(mpr->address)))
						{
							
						}
						else
						{
							insert_into_tco_node_addr_set(&(olsr->recent_add_list), GetIPv4Address(mpr->address));
						}
						
					}
					else
					{
						if (!topo_dest_for_sym->destination_node->topology_destination_info.bAddForNormal)
						{
							topo_dest_for_sym->destination_node->topology_destination_info.bAddForNormal = TRUE;

							//printf("!!!!!!!!!!!! this branch should not exist because of the symmetric property in OlsrUpdateLastTable 2 for dst = %d \n", topo_dest_for_sym->destination_node->topology_destination_info.topology_dst.interfaceAddr.ipv4);
						}
						
						//this branch should not exist because of the symmetric property
						
					}
				
				
					if (g_iSymmetricDifferentCode == 1)
					{

						//for symmetric, add a last entry with address same as this mpr and dest the same as the address of the last_entry
						topology_last_entry *t_last_symmetric = NULL;

						t_last_symmetric = OlsrLookupLastTopologyTableSYM(node, mpr->address);
						if (t_last_symmetric != NULL)
						{
							//already exist
						}
						else
						{
							//create and insert
							t_last_symmetric = (topology_last_entry *)
								MEM_malloc(sizeof(topology_last_entry));

							memset(t_last_symmetric, 0, sizeof(topology_last_entry));


							UInt32 hash_symmetric;
							topology_last_hash* top_last_hash_symmetric;

							RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;


							OlsrHashing(mpr->address, &hash_symmetric);
							top_last_hash_symmetric = &olsr->sym_topologylasttable[hash_symmetric % HASHMASK];

							/* prepare the last entry */
							t_last_symmetric->topology_last = mpr->address;
							t_last_symmetric->topology_list_of_destinations = NULL;
							t_last_symmetric->topologylast_hash = hash_symmetric;
							//t_last_symmetric->topology_seq = message->ansn;

							/*
							t_last_symmetric->topology_timer = getSimTime(node)
							+ (clocktype)(message->vtime * SECOND);
							*/
							

							OlsrInsertList((olsr_qelem *)t_last_symmetric, (olsr_qelem *)top_last_hash_symmetric);

						}	

						//check and add the dest with address 
						destination_list* topo_dest_symmetric = OlsrinListDestTopology(t_last_symmetric, message->originator);
						if (topo_dest_symmetric == NULL)
						{

							destination_list * topo_dest_symmetric = (destination_list *)
								MEM_malloc(sizeof(destination_list));
							memset(topo_dest_symmetric, 0, sizeof(destination_list));


							topo_dest_symmetric->next = t_last_symmetric->topology_list_of_destinations;
							t_last_symmetric->topology_list_of_destinations = topo_dest_symmetric;


							topology_destination_entry * destination_entry_symmetric = (topology_destination_entry *)
								MEM_malloc(sizeof(topology_destination_entry));

							memset(destination_entry_symmetric, 0, sizeof(topology_destination_entry));

							destination_entry_symmetric->topology_destination_dst = message->originator;
							destination_entry_symmetric->topology_destination_list_of_last = NULL;
							
							destination_entry_symmetric->topology_destination_info.bAddForSymmetric = TRUE;

							UInt32 hash_symmetric;

							OlsrHashing(message->originator, &hash_symmetric);

							destination_entry_symmetric->topologydestination_hash = hash_symmetric;


							topo_dest_symmetric->destination_node = destination_entry_symmetric;

						}
						else
						{
							//do not need to add, but this branch may not happen because of the symmetric property

							if (!topo_dest_symmetric->destination_node->topology_destination_info.bAddForSymmetric)
							{
								topo_dest_symmetric->destination_node->topology_destination_info.bAddForSymmetric = TRUE;

								//printf("!!!!!!!!!!!! this branch should not exist because of the symmetric property in OlsrUpdateLastTable 2 for dst = %d \n", topo_dest_for_sym->destination_node->topology_destination_info.topology_dst.interfaceAddr.ipv4);
							}
							//DebugBreak();
							//this branch should not exist because of the symmetric property
							//printf("!!!!!!!!!!!! this branch should not exist because of the symmetric property in OlsrUpdateLastTable 1 \n");
						}
					}
				
				
				}
				else
				{


					//this branch should not exist because of the symmetric property
					printf("!!!!!!!!!!!! this branch should not exist because of the symmetric property in in OlsrUpdateLastTable 3 \n");
				}			

			}


            if (DEBUG)
            {
                char addrString[MAX_STRING_LENGTH];
                IO_ConvertIpAddressToString(&mpr->address,
                                            addrString);

                printf("This mpr is %s\n", addrString);
                if (mpr->next == NULL)
                {
                    printf("the next is NULL\n");
                }
                else
                {
                    printf("the next is not NULL\n");
                }
            }
        }
        mpr = mpr->next;
    }


	//printf("OlsrUpdateLastTable End \n");
}


//SYMMETRIC TOPOLOGY TABLE

static
void OlsrReleaseTopologyTableSYM(
							  Node* node)
{

	Int32 index;

	topology_destination_entry* top_dest;
	topology_destination_entry* top_dest_tmp;
	topology_destination_hash* top_dest_hash;

	topology_last_entry* top_last;
	topology_last_entry* top_last_tmp;
	topology_last_hash* top_last_hash;

	RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

	// delete topology last table
	for (index = 0; index < HASHSIZE; index++)
	{
		top_last_hash = &olsr->sym_topologylasttable[index];
		top_last = top_last_hash->topology_last_forw;
		while (top_last != (topology_last_entry *) top_last_hash)
		{
			top_last_tmp = top_last;
			top_last = top_last->topology_last_forw;
			
			//SYMMETRIC TOPOLOGY TABLE  would be correct
			//Since Here for release the whole table, OlsrDeleteLastTopolgyTableSYM is not required
			//note!!!: correct anyway, since the OlsrReleaseTables that call this function is never called. 
			
			OlsrDeleteLastTopolgyTableSYMInSerial(top_last_tmp);
			//OlsrDeleteLastTopolgyTable(top_last_tmp);
		}
	}
}


// /**
// FUNCTION   :: OlsrReleaseTopologyTable
// LAYER      :: APPLICATION
// PURPOSE    :: releases topology table
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// RETURN :: void : NULL
// **/

static
void OlsrReleaseTopologyTable(
    Node* node)
{


	//printf("OlsrReleaseTopologyTable Begin \n");

    Int32 index;

    topology_destination_entry* top_dest;
    topology_destination_entry* top_dest_tmp;
    topology_destination_hash* top_dest_hash;

    topology_last_entry* top_last;
    topology_last_entry* top_last_tmp;
    topology_last_hash* top_last_hash;

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    // delete topology destination table
    for (index = 0; index < HASHSIZE; index++)
    {
        top_dest_hash = &olsr->topologytable[index];
        top_dest = top_dest_hash->topology_destination_forw;
        while (top_dest != (topology_destination_entry *) top_dest_hash)
        {
            top_dest_tmp = top_dest;
            top_dest = top_dest->topology_destination_forw;
            OlsrDeleteDestTopolgyTable(top_dest_tmp);
        }
    }



	if (SYMMETRIC_TOPOLOGY_TABLE)
	{
		OlsrReleaseTopologyTableSYM(node);
	}



    // delete topology last table
    for (index = 0; index < HASHSIZE; index++)
    {
        top_last_hash = &olsr->topologylasttable[index];
        top_last = top_last_hash->topology_last_forw;
        while (top_last != (topology_last_entry *) top_last_hash)
        {
            top_last_tmp = top_last;
            top_last = top_last->topology_last_forw;
            OlsrDeleteLastTopolgyTable(top_last_tmp);
        }
    }


	//printf("OlsrReleaseTopologyTable End \n");

}

//Peter added for combine...
static
void OlsrReleaseCombinedTopologyTable(
							  Node* node)
{
	Int32 index;

	topology_destination_entry* top_dest;
	topology_destination_entry* top_dest_tmp;
	topology_destination_hash* top_dest_hash;


	RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

	// delete topology destination table
	for (index = 0; index < HASHSIZE; index++)
	{
		top_dest_hash = &olsr->combined_topologytable[index];
		top_dest = top_dest_hash->topology_destination_forw;
		while (top_dest != (topology_destination_entry *) top_dest_hash)
		{
			top_dest_tmp = top_dest;
			top_dest = top_dest->topology_destination_forw;
			OlsrDeleteCombinedDestTopolgyTable(top_dest_tmp);
		}
	}

}

/*
static
void GenerateCombinedTopologyTable(
								   Node* node)
{

	OlsrReleaseCombinedTopologyTable(node);


	Int32 index;

	topology_destination_entry* top_dest;
	topology_destination_entry* top_dest_tmp;
	topology_destination_hash* top_dest_hash;


	RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

	// delete topology destination table
	for (index = 0; index < HASHSIZE; index++)
	{
		top_dest_hash = &olsr->topologytable[index];
		top_dest = top_dest_hash->topology_destination_back;
		while (top_dest != (topology_destination_entry *) top_dest_hash)
		{

			top_dest_tmp = top_dest;
			top_dest = top_dest->topology_destination_back;

			topology_destination_entry* destination_entry = NULL;

			destination_entry = (topology_destination_entry *)
			MEM_malloc(sizeof(topology_destination_entry));

			memset(destination_entry, 0, sizeof(topology_destination_entry));

			
			OlsrInsertCombinedTopologyTable(node, destination_entry, top_dest_tmp->topology_destination_dst);


			last_list* list_of_last;
			
			list_of_last = top_dest_tmp->topology_destination_list_of_last;

			last_list* list_of_last_tmp = NULL;

			while (list_of_last != NULL)
			{

				topology_last_entry * t_last = (topology_last_entry *)
				MEM_malloc(sizeof(topology_last_entry));

				memset(t_last, 0, sizeof(topology_last_entry));

				last_list * topo_last = (last_list *) MEM_malloc(sizeof(last_list));
				memset(topo_last, 0, sizeof(last_list));

				t_last->topology_last = list_of_last->last_neighbor->topology_last; 
				

				topo_last->last_neighbor = t_last;

				topo_last->next = list_of_last_tmp;

				list_of_last_tmp = topo_last;

				list_of_last = list_of_last->next;
			}

			
			
			topology_last_hash* top_last_hash; 
			topology_last_entry* top_last;

			top_last_hash = &olsr->topologylasttable[top_dest_tmp->topologydestination_hash % HASHMASK];

			for (top_last = top_last_hash->topology_last_forw;
				top_last != (topology_last_entry* ) top_last_hash;
				top_last = top_last->topology_last_forw)
			{
				if (top_last->topologylast_hash != top_dest_tmp->topologydestination_hash)
				{
					continue;
				}

				destination_list* top_dest_list;				
				top_dest_list = top_last->topology_list_of_destinations;
				while (top_dest_list != NULL)
				{
					
					if (NULL == OlsrinListLastTopology(top_dest_tmp->topology_destination_list_of_last, 
						top_dest_list->destination_node->topology_destination_dst))
					{

						
						topology_last_entry * t_last = (topology_last_entry *)
						MEM_malloc(sizeof(topology_last_entry));

						memset(t_last, 0, sizeof(topology_last_entry));

						last_list * topo_last = (last_list *) MEM_malloc(sizeof(last_list));
						memset(topo_last, 0, sizeof(last_list));

						t_last->topology_last = top_dest_list->destination_node->topology_destination_dst;

						topo_last->next = list_of_last_tmp;
							
						
						topo_last->last_neighbor = t_last;

						list_of_last_tmp = topo_last;
						
					}
				
					top_dest_list = top_dest_list->next;
				}
				
				 
			}
			

			destination_entry->topology_destination_list_of_last = list_of_last_tmp;
		}
	}

}
*/

//SYMMETRIC TOPOLOGY TABLE

static
void OlsrTimeoutTopologyTableSYM(Node* node)
{

	/*
	if (node->nodeId == 80)
	{

		printf("OlsrTimeoutTopologyTableSYM Begin for node %d \n", node->nodeId);

	}
	*/

	//printf("################################## OlsrTimeoutTopologyTableSYM is called!!!!!!!!!!!!!!!!!!!!!! \n");

	//if (getSimTime(node))

	char timeStr[MAX_STRING_LENGTH];
	TIME_PrintClockInSecond(getSimTime(node), timeStr, node);

	double dSimTime = atof(timeStr);


	BOOL bPrint = FALSE;

	
	//if (node->nodeId == 17 && iSimTime > 35)
	
	if (FALSE)
	//if (node->nodeId == 18)
	{
		


		if (dSimTime > 25)
		{
			//DebugBreak();
			printf("Before TO \n");
			
			g_iChaseRouteTable = 0;
			OlsrPrintTopologyTableSYM(node);
			g_iChaseRouteTable = 1;

			bPrint = TRUE;
		}
		
		
		printf("current node Id = %d at %f S \n", node->nodeId, dSimTime);
		
		
	}
	

	


	Int32 index;
	topology_last_entry* top_last;
	topology_last_entry* top_last_tmp;
	topology_last_hash* top_last_hash;

	RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

	for (index = 0; index < HASHSIZE; index++)
	{

		/*
		if (bPrint && index == 29)
		{

			printf("current index = %d \n", index);
			DebugBreak();
		}
		*/

		top_last_hash = &olsr->sym_topologylasttable[index];
		top_last = top_last_hash->topology_last_forw;
		while (top_last != (topology_last_entry *) top_last_hash)
		{
			
			
			
			// check each tuple for expiration
			if (getSimTime(node) >= top_last->topology_timer)
			{

				//printf("################# nodeId = %d with top_last->topology_last = %d and top_last->topology_timer = %d in OlsrTimeoutTopologyTableSYM \n", node->nodeId, top_last->topology_last.interfaceAddr.ipv4, top_last->topology_timer);
				
				if (top_last->topology_timer == 0)
				{
					top_last = top_last->topology_last_forw;
					//printf("################# nodeId = %d with top_last->topology_timer = 0 \n", node->nodeId);
				}
				else
				{
					top_last_tmp = top_last;
					top_last = top_last->topology_last_forw;



					////SYMMETRIC TOPOLOGY TABLE ???
					

					//the problem may caused by the delete of the top_last_hash, 
					//so the loop can not terminate
					//OlsrDeleteLastTopolgyTableSYM(node, top_last_tmp);
					
					OlsrDeleteLastTopolgyTableSYM(node, top_last_tmp, FALSE);


					if (SYMMETRIC_TOPOLOGY_TABLE)
					{
						//the outsider OlsrTimeoutTopologyTable will set olsr->changes_topology,
						//but if recent_delete_list or recent_add_list is not NULL, then the full RC will not be called.
						if (olsr->recent_delete_list != NULL)
						{
							clear_tco_node_addr_set(&(olsr->recent_delete_list));
						}
						
						if (olsr->recent_add_list != NULL)
						{
							clear_tco_node_addr_set(&(olsr->recent_add_list));
						}
						
						
					}

					//olsr->changes_topology = TRUE;

					
				}				
			}
			else
			{
				top_last = top_last->topology_last_forw;
			}
		}
	}


	if (bPrint)
	{

		printf("After TO \n");

		g_iChaseRouteTable = 0;
		OlsrPrintTopologyTableSYM(node);
		g_iChaseRouteTable = 1;
	}

	/*
	if (node->nodeId == 80)
	{

		printf("OlsrTimeoutTopologyTableSYM End for node %d \n", node->nodeId);

	}
	*/

	////SYMMETRIC TOPOLOGY TABLE
	//May still require to delete the symmetric corresponding dest of entries 
}



// /**
// FUNCTION   :: OlsrTimeoutTopologyTable
// LAYER      :: APPLICATION
// PURPOSE    :: This function will be called
//               when olsr->top_hold_timer expires
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// RETURN :: void : NULL
// **/

static
void OlsrTimeoutTopologyTable(
    Node* node)
{
    // We only check last table because we didn't include a time out in the
    // dest entries

	//Peter comment: just test 
	//return;


	//printf("OlsrTimeoutTopologyTable Begin \n");

    Int32 index;
    topology_last_entry* top_last;
    topology_last_entry* top_last_tmp;
    topology_last_hash* top_last_hash;

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

	if (SYMMETRIC_TOPOLOGY_TABLE)
	{
		OlsrTimeoutTopologyTableSYM(node);
	}


    for (index = 0; index < HASHSIZE; index++)
    {
        top_last_hash = &olsr->topologylasttable[index];
        top_last = top_last_hash->topology_last_forw;
        while (top_last != (topology_last_entry *) top_last_hash)
        {
            // check each tuple for expiration
            if (getSimTime(node) >= top_last->topology_timer)
            {
                top_last_tmp = top_last;
                top_last = top_last->topology_last_forw;
                OlsrDeleteLastTopolgyTable(top_last_tmp);
                olsr->changes_topology = TRUE;
                
				g_iTopologyChgByOlsrTimeoutTopologyTable++;

            }
            else
            {
                top_last = top_last->topology_last_forw;
            }
        }
    }


	//printf("OlsrTimeoutTopologyTable End \n");
}



//SYMMETRIC TOPOLOGY TABLE


static
void OlsrPrintTopologyTableSYM(
							Node* node)
{

	/*
	if (node->nodeId == 1)
	{
		//DebugBreak();
	}
	*/
	

	Int32 index;
	topology_last_entry* top_last;
	topology_last_hash* top_last_hash;
	destination_list* top_dest_list;

	RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;


	if (g_iRunTimeCompare == 1)
	{
		sprintf(olsr->pszOtherTables, "SYM Topology Table:\n");
	}
	else
	{
		if (g_iChaseRouteTable == 1)
		{
			memset(g_szTextRT, 0, 16384 * sizeof(char));
			sprintf(g_szTextRT, "SYM Topology Table:\n");
		}
		else
		{
			printf("SYM Topology Table:\n");
		}
	}
	

	

	for (index = 0; index < HASHSIZE; index++)
	{
		top_last_hash = &olsr->sym_topologylasttable[index];
		for (top_last = top_last_hash->topology_last_forw;
			top_last != (topology_last_entry *) top_last_hash;
			top_last = top_last->topology_last_forw)
		{
			char addrString[MAX_STRING_LENGTH];

			IO_ConvertIpAddressToString(&top_last->topology_last,
				addrString);


			if (g_iRunTimeCompare == 1)
			{
				sprintf(olsr->pszOtherTables, "%s%-15s: [last_hop_of: ", olsr->pszOtherTables, addrString);
			}
			else
			{
				if (g_iChaseRouteTable == 1)
				{
					sprintf(g_szTextRT, "%s%-15s: [last_hop_of: ",g_szTextRT, addrString);
				}
				else
				{
					printf("%-15s: [last_hop_of: ",addrString);
				}
			}
			

			
			top_dest_list = top_last->topology_list_of_destinations;

			while (top_dest_list != NULL)
			{
				IO_ConvertIpAddressToString(
					&top_dest_list->destination_node->
					topology_destination_dst, addrString);

				//printf("%s (%d %d)", addrString, top_dest_list->destination_node->topology_destination_info.bAddForSymmetric, top_dest_list->destination_node->topology_destination_info.bAddForNormal);
				
				if (g_iRunTimeCompare == 1)
				{
					sprintf(olsr->pszOtherTables, "%s%s ", olsr->pszOtherTables, addrString);
				}
				else
				{
					if (g_iChaseRouteTable == 1)
					{
						sprintf(g_szTextRT, "%s%s ", g_szTextRT, addrString);
					}
					else
					{
						printf("%s ", addrString);
					}
				}
								
				top_dest_list = top_dest_list->next;
			}


			if (g_iRunTimeCompare == 1)
			{
				sprintf(olsr->pszOtherTables,"%s]\n", olsr->pszOtherTables);
			}
			else
			{
				if (g_iChaseRouteTable == 1)
				{
					sprintf(g_szTextRT,"%s]\n", g_szTextRT);
				}
				else
				{
					printf("]\n");
				}
			}
			
			
		}
	}

}



// /**
// FUNCTION   :: OlsrPrintTopologyTable
// LAYER      :: APPLICATION
// PURPOSE    :: Prints topology table
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// RETURN :: void : NULL
// **/

static
void OlsrPrintTopologyTable(
    Node* node)
{
    Int32 index;
    topology_last_entry* top_last;
    topology_last_hash* top_last_hash;
    destination_list* top_dest_list;

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    printf("Topology Table:\n");
    for (index = 0; index < HASHSIZE; index++)
    {
        top_last_hash = &olsr->topologylasttable[index];
        for (top_last = top_last_hash->topology_last_forw;
            top_last != (topology_last_entry *) top_last_hash;
            top_last = top_last->topology_last_forw)
        {
            char addrString[MAX_STRING_LENGTH];

            IO_ConvertIpAddressToString(&top_last->topology_last,
                                        addrString);

            printf("%-15s: [last_hop_of: ",addrString);
            top_dest_list = top_last->topology_list_of_destinations;

            while (top_dest_list != NULL)
            {
                IO_ConvertIpAddressToString(
                    &top_dest_list->destination_node->
                        topology_destination_dst, addrString);

                printf("%s ", addrString);
                top_dest_list = top_dest_list->next;
            }
            printf("]\n");
        }
    }
}


// Peter Added for support _OLSR_MULTIPATH

static
void OlsrPrintDestTopologyTable(
							Node* node)
{
	Int32 index;
	topology_destination_entry* top_dest;
	topology_destination_hash* top_dest_hash;
	UInt32 hash;

	RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

	if (DEBUG)
	{
		printf("OlsrPrintRealTopologyTable\n");
	}

	//OlsrHashing(dest, &hash);

	//destination_list* top_dest_list;
	last_list *list_of_last;

	printf("Dest Topology Table:\n");
	for (index = 0; index < HASHSIZE; index++)
	{
		top_dest_hash = &olsr->topologytable[index];
		for (top_dest = top_dest_hash->topology_destination_forw;
			top_dest != (topology_destination_entry *) top_dest_hash;
			top_dest = top_dest->topology_destination_forw)
		{
			printf("%d ", top_dest->topologydestination_hash);
			

			char addrString[MAX_STRING_LENGTH];

			IO_ConvertIpAddressToString(&top_dest->topology_destination_dst,
				addrString);

			printf("%-15s: [dest_hop_of: ",addrString);

			list_of_last = top_dest->topology_destination_list_of_last;
			
			//top_dest_list = top_last->topology_list_of_destinations;

			while (list_of_last != NULL)
			{
				//list_of_last->last_neighbor->		topologylast_hash	
				//IO_ConvertIpAddressToString(&list_of_last->last_neighbor->topologylast_hash, addrString);

				printf("%d ", list_of_last->last_neighbor->topologylast_hash);
				list_of_last = list_of_last->next;
			}
			//topology_destination_list_of_last
			printf("\n");

		}

	}
}

static
void OlsrPrintCombinedTopologyTable(
								Node* node)
{
	Int32 index;
	topology_destination_entry* top_dest;
	topology_destination_hash* top_dest_hash;
	UInt32 hash;

	RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

	if (DEBUG)
	{
		printf("OlsrPrintRealTopologyTable\n");
	}

	last_list *list_of_last;

	printf("Combined Topology Table:\n");
	for (index = 0; index < HASHSIZE; index++)
	{
		top_dest_hash = &olsr->combined_topologytable[index];
		for (top_dest = top_dest_hash->topology_destination_forw;
			top_dest != (topology_destination_entry *) top_dest_hash;
			top_dest = top_dest->topology_destination_forw)
		{
			printf("%d ", top_dest->topologydestination_hash);


			char addrString[MAX_STRING_LENGTH];

			IO_ConvertIpAddressToString(&top_dest->topology_destination_dst,
				addrString);

			printf("%-15s: [last_hop_of: ",addrString);

			list_of_last = top_dest->topology_destination_list_of_last;


			while (list_of_last != NULL)
			{

				//memset(addrString, 0, MAX_STRING_LENGTH * sizeof(char));

				//IO_ConvertIpAddressToString(&list_of_last->last_neighbor->topology_last, addrString);


				//Address* dsf;
				//dsf->interfaceAddr.ipv4

				printf("%d ", list_of_last->last_neighbor->topology_last.interfaceAddr.ipv4);


				list_of_last = list_of_last->next;
			}

			printf("\n");

		}
	}
}


static
//int 
void OlsrLookupAndUpdateRoutingCount(
								 Node* node,
								 Address dst)
{

	//Peter Comment: we try to only use the first entry to contain those
	//infos

	rt_entry* destination;
	rthash* routing_hash;
	UInt32 hash;

	RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

	OlsrHashing(dst, &hash);
	routing_hash = &olsr->routingtable[hash % HASHMASK];


	//UInt16 iRouteCnt = 0;

	
	for (destination = routing_hash->rt_back;
		destination != (rt_entry* ) routing_hash;
		destination = destination->rt_back)
	{
		if (destination->rt_hash != hash)
		{
			continue;
		}

		// search address in the routing table entry
		if (Address_IsSameAddress(&destination->rt_dst, &dst))
		{

			destination->rt_entry_infos.oa_total_routes_count++;						
		}

		//since this is the only case, so break here.
		break;
	}
	

	return;
	
	//iRouteCnt++;

	//return iRouteCnt;	
}


/***************************************************************************
 *                   Defination of Routing Table                           *
 ***************************************************************************/
// /**
// FUNCTION   :: OlsrLookupRoutingTable
// LAYER      :: APPLICATION
// PURPOSE    :: Searches in the routing table for this address
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + dst : Address : Address to be looked up
// RETURN :: rt_entry* : Pointer to entry if found, else NULL
// **/

static
rt_entry* OlsrLookupRoutingTable(
    Node* node,
    Address dst, BOOL bForCompare = FALSE)
{
    rt_entry* destination;
    rthash* routing_hash;
    UInt32 hash;

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    OlsrHashing(dst, &hash);

	if (bForCompare)
	{
		routing_hash = &olsr->mirror_table[hash % HASHMASK];
	}
	else
	{
		routing_hash = &olsr->routingtable[hash % HASHMASK];
	}

    

    for (destination = routing_hash->rt_forw;
        destination != (rt_entry* ) routing_hash;
        destination = destination->rt_forw)
    {
        if (destination->rt_hash != hash)
        {
            continue;
        }

        // search address in the routing table entry
        if (Address_IsSameAddress(&destination->rt_dst, &dst))
        {
            return destination;
        }
    }
    return NULL;
}


static
rt_entry* OlsrLookupRoutingTableAdv(
								 Node* node,
								 Address dst,
								 Int16 iExpectedCost = MAX_COST)
{
	//printf("=========== OlsrLookupRoutingTableAdv Start \n");

	rt_entry* destination;
	rthash* routing_hash;
	UInt32 hash;

	RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

	OlsrHashing(dst, &hash);
	routing_hash = &olsr->routingtable[hash % HASHMASK];

	for (destination = routing_hash->rt_forw;
		destination != (rt_entry* ) routing_hash;
		destination = destination->rt_forw)
	{
		if (destination->rt_hash != hash)
		{
			continue;
		}

		// search address in the routing table entry
		if (Address_IsSameAddress(&destination->rt_dst, &dst))
		{
		
			if (destination->rt_metric > iExpectedCost)
			{
				//remove the current route entry, since its cost is not optimized
				OlsrDeleteRoutingTable(destination);

				break;
			}
			else
			{

				return destination;
			}			
		}
	}

	//printf("=========== OlsrLookupRoutingTableAdv End \n");

	return NULL;
}


static
rt_entry* OlsrLookupRoutingTableAdvForLastReplace(
	Node* node,
	Address dst,
	Address lasthop,
	Address router,
	Int16 iExpectedCost,
	BOOL bOnlyCommonLast = FALSE, BOOL bRequireSameRouter = FALSE, rt_entry** ppre = NULL)
{

	rt_entry* Conclude = NULL;
	rt_entry* destination;
	rthash* routing_hash;
	UInt32 hash;

	RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

	OlsrHashing(dst, &hash);
	routing_hash = &olsr->routingtable[hash % HASHMASK];

	for (destination = routing_hash->rt_back;
		destination != (rt_entry* ) routing_hash;
		destination = destination->rt_back)
	{
		if (destination->rt_hash != hash)
		{
			continue;
		}

		if (Conclude == NULL)
		{
			Conclude = destination;

			if (ppre != NULL)
			{
				*ppre = destination;
			}
		}

		// search address in the routing table entry	
		if (Address_IsSameAddress(&destination->rt_dst, &dst))
		{

			if (bOnlyCommonLast)
			{
				if (!bRequireSameRouter && destination->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 == lasthop.interfaceAddr.ipv4
					|| bRequireSameRouter && destination->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 == lasthop.interfaceAddr.ipv4 && Address_IsSameAddress(&destination->rt_router, &router)) 
					//&& (destination->rt_entry_infos.rtu_router.interfaceAddr.ipv4 != router.interfaceAddr.ipv4 
					//	|| destination->rt_entry_infos.rtu_metric != iExpectedCost))
				{

					return destination;				
				}
				
			}
						
		}		
	}

	return NULL;
}

//#ifdef _OLSR_MULTIPATH
//Peter Modified: this function is used for caculate routing table with supporting multi-path
/*
BOOL OlsrTwoRoutersAreNeighbour(Node* node, Address route1, Address route2)
{

	//Peter comment: search from last table that match with one route,
	//so as to compare its destination with the other route to see whether one can reach 
	//the other directly (so that two routes are too near that need to be avoided)

	BOOL bReachable = FALSE;

	topology_last_entry* top_last = NULL;
	destination_list* top_dest_list = NULL;

	top_last = OlsrLookupLastTopologyTable(node, route1);
	
	if (top_last != NULL)
	{
		top_dest_list = top_last->topology_list_of_destinations;

		BOOL bReachable = FALSE; 
		while (top_dest_list != NULL)
		{

			//skip the route that within 1 hop distance from current route
			if (Address_IsSameAddress(&top_dest_list->destination_node->topology_destination_dst, &route2))
			{

				bReachable = TRUE;
				break;
			}							

			top_dest_list = top_dest_list->next;
		}			
	}

	
	if (bReachable)
	{

		return bReachable;
	}


	top_last = NULL;
	top_dest_list = NULL;

	top_last = OlsrLookupLastTopologyTable(node, route2);

	if (top_last != NULL)
	{
		top_dest_list = top_last->topology_list_of_destinations;

		BOOL bReachable = FALSE; 
		while (top_dest_list != NULL)
		{

			//skip the route that within 1 hop distance from current route
			if (Address_IsSameAddress(&top_dest_list->destination_node->topology_destination_dst, &route1))
			{

				bReachable = TRUE;
				break;
			}							

			top_dest_list = top_dest_list->next;
		}			
	}
	

	return bReachable;
}
*/


RouteEntryType OlsrAdvancedLookupRoutingTable(Node* node, Address dst, Address route, UInt16 expected_metric, double dRouteDegreeWRTOriginNode, UInt16 uiMaxRouterCount, Address last, BOOL bUpdateForAddList = FALSE, rt_entry** pprte = NULL)
{

	/*
	char timeStr[MAX_STRING_LENGTH];
	TIME_PrintClockInSecond(getSimTime(node), timeStr, node);

	int iSimTime = atoi(timeStr);

	if (iSimTime > 20 && node->nodeId == 2 && dst.interfaceAddr.ipv4 == 5)
	{

		//DebugBreak();
	}
	*/

	RouteEntryType ret = ALLOWED_NORMAL;

	if (pprte != NULL)
	{
		*pprte = NULL;
	}
	
	//first of all, check the cost limitation

	//Peter comment: two entries with same dest, different router, but the cost of new entry
	//is not only one hop more than smallest of current exist one, may cause too many paths 
	//or some unexpected long path in the future, so this condition is also not permitted 

	//For 2 Hop case, the cost should be same uiHopCountDiff == 0 ???
	//For more than 2 Hop case, uiHopCountDiff >=0


	//!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
	//Because the Topology table in OLSR is "not always" (worse than never or always, since it is random) symmetric.
	//For example: in 4x4 topology, node 16 is in node 12's lasttop table, but node 16 itself does not have lasttop table,
	//so according to routing table calculation, 16 can not reach 12 but 12 can reach 16.
	
	//	-- May need check the code to see how was the Topology table generated.

	//	Different entries with same route (nextHop)  is not allowed:

	//(1) cost == min:  allow same lastHop       allow further search (add to working set)
	//(2) cost > min: disallow same lastHop      do not allow further search (do not add to working set)

	//If the topology table can be modified to support symmetric, we can dis-allow different route & different lasthop
	//for both (1) and (2), and only based on cost to determine further search(may need in-depth study for exceptions) 

	rt_entry* destination;
	rthash* routing_hash;

	UInt32 hash;

	RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

	OlsrHashing(dst, &hash);
	routing_hash = &olsr->routingtable[hash % HASHMASK];



	//Peter comment: search from last table that match with the new route,
	//so as to compare its destination with the old route to see whether the new route 
	//can reach old route directly (so there two routes are too near that need to be avoided)
	//See function OlsrTwoRoutersAreNeighbour for detail
	

	//Just try whether there is one existing router that can not reached by this new one.
	//BOOL bExistCanNotReachRouter = FALSE;
	//BOOL bAlreadyExistOtherRoutersToSameDestination = FALSE;

	

	rt_entry* First_destination = NULL;


	for (destination = routing_hash->rt_back;
		destination != (rt_entry* ) routing_hash;
		destination = destination->rt_back)
	{
		if (destination->rt_hash != hash)
		{

			continue;
		}

		if (First_destination == NULL)
		{
			First_destination = destination;

			if (First_destination->rt_entry_infos.oa_maximum_allowed_cost == 0)
			{

				First_destination->rt_entry_infos.oa_maximum_allowed_cost = max(((double)(First_destination->rt_metric + MAX_DIFFEERENT_ROUTE_HOP_COUNT_DIFFERENCE)), ceil((double)(First_destination->rt_metric) * (double) MAX_DIFFEERENT_ROUTE_HOP_COUNT_DIFFERENCE_TIMES));
			}

			/*
			if (First_destination->rt_entry_infos.oa_total_routes_count == 1 && First_destination->rt_entry_infos.oa_dWeightedDirectionDiffer == 0.0)
			{

				
			}
			*/
		}

		if (!bUpdateForAddList)
		{
			if (First_destination->rt_entry_infos.oa_total_routes_count == uiMaxRouterCount)
			{

				return NOT_ALLOWED;
			}

			if (First_destination->rt_entry_infos.oa_maximum_allowed_cost < expected_metric)
			{

				return NOT_ALLOWED;
			}

			// search address in the routing table entry
			if (Address_IsSameAddress(&destination->rt_dst, &dst))
			{			


				if (Address_IsSameAddress(&destination->rt_router, &route))
				{
					//Peter comment: two entries with same dest and same router are not permitted

					return NOT_ALLOWED;	
				}



				double dDgrWRT = 0.0;
				if (_TEST_TIME_COMPLEXITY)
				{
					dDgrWRT = First_destination->rt_entry_infos.related_neighbor->neighbor_infos.dDegreeWRTNode;

				}
				else
				{
					dDgrWRT = First_destination->rt_entry_infos.rtu_DegreeWRTNode;

				}

				//Peter Modified to support disjoint path, only try to use shortest path now.					
				double dDiff = RadiusDegreeDifference(dRouteDegreeWRTOriginNode, 
					dDgrWRT);

				if (fabs(dDiff) < olsr->dSectorDegree)
				{

					return NOT_ALLOWED;
				}			
			}
		}
		else
		{
			

			/*
			if (First_destination->rt_entry_infos.oa_total_routes_count == uiMaxRouterCount)
			{

				return NOT_ALLOWED;
			}
			*/

			if (First_destination->rt_entry_infos.oa_maximum_allowed_cost < expected_metric)
			{

				return NOT_ALLOWED;
			}

			
			// search address in the routing table entry
			if (Address_IsSameAddress(&destination->rt_dst, &dst))
			{			


				if (Address_IsSameAddress(&destination->rt_router, &route))
				{
					//Peter comment: two entries with same dest and same router are not permitted

					//return NOT_ALLOWED;
					if (expected_metric >= destination->rt_metric)
					{
						
						return NOT_ALLOWED;
					}
					else
					{
						destination->rt_entry_infos.rtu_metric = expected_metric;
						destination->rt_entry_infos.rtu_lasthop = last;
						
						*pprte = destination;

					}
				}
				else
				{
					
				}



				double dDgrWRT = 0.0;
				if (_TEST_TIME_COMPLEXITY)
				{
					dDgrWRT = First_destination->rt_entry_infos.related_neighbor->neighbor_infos.dDegreeWRTNode;

				}
				else
				{
					dDgrWRT = First_destination->rt_entry_infos.rtu_DegreeWRTNode;

				}

				//Peter Modified to support disjoint path, only try to use shortest path now.					
				double dDiff = RadiusDegreeDifference(dRouteDegreeWRTOriginNode, 
					dDgrWRT);

				if (fabs(dDiff) < olsr->dSectorDegree)
				{

					return NOT_ALLOWED;
				}			
			}


		}

		
	}


	//Update the allowed Angle range
	//May not require
	
	//olsr->dSectorDegree
	if (First_destination != NULL)
	{
		//at least the second one now

				
		double dAccumulatedWeightedDiffer = First_destination->rt_entry_infos.oa_dWeightedDirectionDiffer 
										* (double)(First_destination->rt_entry_infos.oa_total_routes_count - 1);
		

		UInt16 uiCostDiff = expected_metric - First_destination->rt_entry_infos.rtu_metric;

		double dWeight = (double)(((double)1.0) / (double)((uiCostDiff + 1) * (uiCostDiff + 1)));

        double dDgrWRT = 0.0;
		if (_TEST_TIME_COMPLEXITY)
        {
                      dDgrWRT = First_destination->rt_entry_infos.related_neighbor->neighbor_infos.dDegreeWRTNode;
                      
        }
        else
        {
                      dDgrWRT = First_destination->rt_entry_infos.rtu_DegreeWRTNode;
                      
        }

		dAccumulatedWeightedDiffer += RadiusDegreeDifference(dRouteDegreeWRTOriginNode, dDgrWRT) * dWeight;
										
		First_destination->rt_entry_infos.oa_dWeightedDirectionDiffer = (double)(dAccumulatedWeightedDiffer 
																/ ((double)(First_destination->rt_entry_infos.oa_total_routes_count)));
		
		

	}

	if (bUpdateForAddList)
	{
		if (*pprte != NULL)
		{
			//exchange and already updated
		}
		else
		{
			if (First_destination)
			{
				if (First_destination->rt_entry_infos.oa_total_routes_count == uiMaxRouterCount)
				{

					return NOT_ALLOWED;
				}

			}
		}

		/*
			
			*/
	}
	
	return ret;	

}


//#endif

// /**
// FUNCTION   :: OlsrDeleteRoutingTable
// LAYER      :: APPLICATION
// PURPOSE    :: Deletes the entry from routing table
// PARAMETERS ::
// + destination : rt_entry* : Pointer to entry
// RETURN :: void : NULL
// **/

static
void OlsrDeleteRoutingTable(
    rt_entry* destination)
{
    OlsrRemoveList((olsr_qelem *)destination);
    MEM_free((void *)destination);
}

// /**
// FUNCTION   :: OlsrReleaseRoutingTable
// LAYER      :: APPLICATION
// PURPOSE    :: Releases the routing table
// PARAMETERS ::
// + table : rthash* : Pointer to routing table
// RETURN :: void : NULL
// **/

static
void OlsrReleaseRoutingTable(
    rthash* table)
{
    rt_entry* destination;
    rt_entry* destination_tmp;
    rthash* routing_hash;

    unsigned char index;

    for (index = 0; index < HASHSIZE; index++)
    {
        routing_hash = &table[index];
        destination = routing_hash->rt_forw;
        while (destination != (rt_entry *) routing_hash)
        {
            destination_tmp = destination;
            destination = destination->rt_forw;

            // deletes each routing entry from the table
            OlsrDeleteRoutingTable(destination_tmp);
        }
    }
}

// /**
// FUNCTION   :: OlsrInsertRoutingTable
// LAYER      :: APPLICATION
// PURPOSE    :: Inserts the address in the routing table
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + dst : Address : address to be inserted
// RETURN :: rt_entry* : Pointer to entry added
// **/

static
rt_entry* OlsrInsertRoutingTable(
    Node* node,
    Address dst, BOOL bForCompare = FALSE)
{
    rt_entry* new_route_entry;
    rthash* routing_hash;
    UInt32 hash;

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    OlsrHashing(dst, &hash);


	if (bForCompare)
	{
		routing_hash = &olsr->mirror_table[hash % HASHMASK];
	}
	else
	{
		routing_hash = &olsr->routingtable[hash % HASHMASK];
	}

    

    new_route_entry = (rt_entry*) MEM_malloc(sizeof(rt_entry));
    memset(new_route_entry, 0, sizeof(rt_entry));

    new_route_entry->rt_hash = hash;

    new_route_entry->rt_dst = dst;

    // No timeout is needed since the routing table is calculated for each
    // network change

    new_route_entry->rt_metric = 0;


	//Peter modified for accumulative re-discovery, for delete case
	new_route_entry->rt_entry_infos.bCostChanged = FALSE;
	new_route_entry->rt_entry_infos.bDescendentRequireFurtherUpdate = FALSE;
	new_route_entry->rt_entry_infos.bRequireDelete = FALSE;

	new_route_entry->rt_entry_infos.uiCostChg = 0;
	//new_route_entry->rt_entry_infos.bRequireExchange = FALSE;
	//new_route_entry->rt_entry_infos.bRequireUpdate = FALSE;

	
			
    OlsrInsertList((olsr_qelem* )new_route_entry,(olsr_qelem *)routing_hash);


	if (bForCompare)
	{

	}
	else
	{

		if (_OLSR_MULTIPATH)
		{

			//Every new entry set this field as 1, but Only the first entry is used for this number later
			new_route_entry->rt_entry_infos.oa_total_routes_count = 0;

			OlsrLookupAndUpdateRoutingCount(node, dst);
		}
		
	}


    // We need this pointer to use it for the next routing calculation
    return new_route_entry;
}

// /**
// FUNCTION   :: OlsrInsertRoutingTablefromTopology
// LAYER      :: APPLICATION
// PURPOSE    :: Inserts the address in the routing table from topology
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + r_last : rt_entry* : Pointer to routing entry
// + dst : Address : destination address
// RETURN :: rt_entry* : pointer to the entry if added, else NULL
// **/

static rt_entry*
OlsrInsertRoutingTablefromTopology(
    Node* node,
    rt_entry* r_last,
    Address dst,
	// Peter Added: For _OLSR_MULTIPATH
	Address lasthop,
	double dRouterDegreeWRTOriginNode = 0,
	double dRouterDistanceWRTOriginNode = 0,
	BOOL bForCompare = FALSE
	)
{
    rt_entry* new_route_entry = NULL;

    ERROR_Assert(r_last, "Invalid topology entry");

    if (DEBUG)
    {
        printf("Insertion from the topology\n");
    }



    if (DEBUG)
    {
        char addrString[MAX_STRING_LENGTH];
        char addrString1[MAX_STRING_LENGTH];

        IO_ConvertIpAddressToString(&dst,
                addrString);
        IO_ConvertIpAddressToString(&r_last->rt_router,
                addrString1);

        printf("Looking up connection to %s for dest %s\n",
                addrString1, addrString);
    }

    if (DEBUG)
    {
        OlsrPrintLinkSet(node);
    }

    // Lookup best link to get to the router
    link_entry* link = OlsrGetLinktoNeighbor(node, r_last->rt_router);

    if (link == NULL)
    {
        printf(" No link exists to looked up neighbor\n");
        return NULL;
    }

    // Only if a link exists to the neighbor, add the node to the routing
    // table.

    new_route_entry = OlsrInsertRoutingTable(node, dst, bForCompare);
    new_route_entry->rt_router = r_last->rt_router;
    new_route_entry->rt_metric = (UInt16) (r_last->rt_metric + 1);
    new_route_entry->rt_interface =  RoutingOlsrCheckMyIfaceAddress(
                                        node,
                                        link->local_iface_addr);

	new_route_entry->rt_entry_infos.rtu_lasthop = lasthop;


	if (_OLSR_MULTIPATH)
	{

		new_route_entry->rt_entry_infos.rtu_DegreeWRTNode = dRouterDegreeWRTOriginNode;
		new_route_entry->rt_entry_infos.rtu_DistanceWRTNode = dRouterDistanceWRTOriginNode;
		new_route_entry->rt_entry_infos.related_neighbor = r_last->rt_entry_infos.related_neighbor;

	}

	
    if (DEBUG)
    {
        char addrString1[MAX_STRING_LENGTH];
        char addrString2[MAX_STRING_LENGTH];

        IO_ConvertIpAddressToString(&dst,
            addrString1);
        IO_ConvertIpAddressToString(&new_route_entry->rt_router,
            addrString2);

        printf("Updating Routing Table at node %d\n", node->nodeId);
        printf("Dst : %s Next Hop : %s Interface: %d Metric: %d\n",
            addrString1,
            addrString2,
            new_route_entry->rt_interface,
            new_route_entry->rt_metric);
    }


	if (_TEST_TIME_COMPLEXITY || FORWARD_WITH_PURE_ROUTE_TABLE)
	{
	}
	else
	{
	
		if (dst.networkType == NETWORK_IPV6)
		{
			Ipv6UpdateForwardingTable(
				node,
				GetIPv6Address(dst),
				128,
				GetIPv6Address(new_route_entry->rt_router),
				new_route_entry->rt_interface,
				new_route_entry->rt_metric,
				ROUTING_PROTOCOL_OLSR_INRIA);

		}
		else
		{
			if (_OLSR_MULTIPATH)
			{

				OLSRv1UpdateForwardingTableWithDisjointPath(node, new_route_entry);
			}
			else
			{

				NetworkUpdateForwardingTable(
					node,
					GetIPv4Address(dst),
					0xffffffff,
					GetIPv4Address(new_route_entry->rt_router),
					new_route_entry->rt_interface,
					new_route_entry->rt_metric,
					ROUTING_PROTOCOL_OLSR_INRIA);
			}


		}

	}


    

	


    return new_route_entry;
}


// /**
// FUNCTION   :: OlsrIs2HopNeighborReachable
// LAYER      :: APPLICATION
// PURPOSE    :: Check if  a two hop neighbor is reachable through a i
//               1 hop neighbor with willingness != WILL NEVER
// PARAMETERS ::
// + neigh_2_list : neighbor_2_list_entry* : Pointer to two hop neighbor
//                                           entry
// RETURN :: bool : true if reachable, else false
// **/


static
bool OlsrIs2HopNeighborReachable(
    neighbor_2_list_entry* neigh_2_list)
{
    neighbor_list_entry* neighbors;

    neighbors = neigh_2_list->neighbor_2->neighbor_2_nblist;

    while (neighbors != NULL)
    {
        if ((neighbors->neighbor->neighbor_status != NOT_NEIGH)
             && (neighbors->neighbor->neighbor_willingness != WILL_NEVER))
        {
            return true;
        }

        neighbors = neighbors->neighbor_next;
    }

    return false;
}


// /**
// FUNCTION   :: OlsrFillRoutingTableWith2HopNeighbors
// LAYER      :: APPLICATION
// PURPOSE    :: Adds two hop neighbors and returns the entries in the list
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// RETURN :: destination_n * :  Pointer to list
// **/

static
destination_n* OlsrFillRoutingTableWith2HopNeighbors(
    Node* node, UInt32 * uiLookupCntFor2Hop = NULL, BOOL bForCompare = FALSE)
{


	UInt32 uiCnt = 0;

    destination_n* list_destination_n = NULL;


	destination_n* tmp_destination_tail = NULL;

    unsigned char index;
    neighbor_entry* neighbor;
    neighborhash_type* hash_neighbor;

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    for (index = 0; index < HASHSIZE; index++)
    {
        hash_neighbor = &olsr->neighbortable.neighborhash[index];

        for (neighbor = hash_neighbor->neighbor_forw;
            neighbor != (neighbor_entry *) hash_neighbor;
            neighbor = neighbor->neighbor_forw)
        {
            neighbor_2_list_entry* neigh_2_list;

            if (neighbor->neighbor_status != SYM)
            {
                continue;
            }

            neigh_2_list = neighbor->neighbor_2_list;
            while (neigh_2_list != NULL)
            {
                Address n2_addr;
                mid_address addrs;
                memset( &addrs, 0, sizeof(mid_address));
                mid_address* addrsp;

                n2_addr = neigh_2_list->neighbor_2->neighbor_2_addr;

                if (DEBUG)
                {
                    char addrString[MAX_STRING_LENGTH];
                    IO_ConvertIpAddressToString(&n2_addr,
                            addrString);

                    printf("Checking Node  %s\n",
                            addrString);
                }

                
				// Peter Modified to support multipath
				//rt_entry* tr_tmp = NULL;
				RouteEntryType ret = NOT_ALLOWED;

                double dDistance = 0.0;
				double dRWON = 0.0;

				
				if (_OLSR_MULTIPATH)
				{
					if (_TEST_TIME_COMPLEXITY)
					{
						dRWON = neighbor->neighbor_infos.dDegreeWRTNode;
						dDistance = neighbor->neighbor_infos.dDistanceWRTNode;
					}
					else
					{
						dRWON = ComputeRouterDegreeWRTOriginNode(node, neighbor->neighbor_main_addr.interfaceAddr.ipv4, &dDistance);
						dRWON = SimulateLocalDirectionOfAoA(node, dRWON);

					}
				}
						

								
				
				if (_TEST_TIME_COMPLEXITY && uiLookupCntFor2Hop != NULL)
				{						
					uiCnt++;


					/*
					if (uiCnt > 5)
					{
						printf("uiCnt = %d \n", uiCnt);

					}
					*/
					
				}
				
				
				if (_OLSR_MULTIPATH)
				{
								
					ret = OlsrAdvancedLookupRoutingTable(node, n2_addr, neighbor->neighbor_main_addr, 2, 
                                                dRWON, 
                                                _OLSR_TEMP_ROUTES_LIMIT, neighbor->neighbor_main_addr);
					if (ret == NOT_ALLOWED)
					{
						neigh_2_list = neigh_2_list->neighbor_2_next;
						continue;
					}
				}
				else
				{

					if (OlsrLookupRoutingTable(node, n2_addr, bForCompare))
					{

						neigh_2_list = neigh_2_list->neighbor_2_next;
						continue;
					}
				}							

                if (!OlsrIs2HopNeighborReachable(neigh_2_list))
                {
                    neigh_2_list = neigh_2_list->neighbor_2_next;
                    continue;
                }

                addrs.alias = n2_addr;
                addrs.next_alias = OlsrLookupMidAliases(node,n2_addr);
                addrsp = &addrs;

                while (addrsp!=NULL)
                {
                    link_entry* link = OlsrGetBestLinktoNeighbor(
                                           node,
                                           neighbor->neighbor_main_addr);

                    if (link)
                    {
                        // Peter modified to support multipath						
						
						rt_entry* new_route_entry = OlsrInsertRoutingTable(node, addrsp->alias, bForCompare);

                        new_route_entry->rt_router = link->neighbor_iface_addr;

						new_route_entry->rt_entry_infos.rtu_lasthop = link->neighbor_iface_addr;


						if (_OLSR_MULTIPATH)
						{
							if (_TEST_TIME_COMPLEXITY)
							{
								new_route_entry->rt_entry_infos.related_neighbor = neighbor;					

							}
							else
							{
								new_route_entry->rt_entry_infos.rtu_DegreeWRTNode = dRWON;

								new_route_entry->rt_entry_infos.rtu_DistanceWRTNode = dDistance;

							}
						}
												
                                                
                        // The next router is the neighbor itself
                        new_route_entry->rt_metric = 2;

                        new_route_entry->rt_interface =
                             RoutingOlsrCheckMyIfaceAddress(
                                node,
                                link->local_iface_addr);

                        if (DEBUG)
                        {
                            char addrString1[MAX_STRING_LENGTH];
                            char addrString2[MAX_STRING_LENGTH];
                            IO_ConvertIpAddressToString(&addrsp->alias,
                                addrString1);
                            IO_ConvertIpAddressToString(
                                &link->neighbor_iface_addr,
                                addrString2);
                            printf("Updating Routing Table at node %d\n",
                                node->nodeId);
                            printf("Dst : %s Next Hop : %s Interface: %d"
                                " Metric: %d\n",
                                addrString1,
                                addrString2,
                                new_route_entry->rt_interface,
                                new_route_entry->rt_metric);
                        }

						if (_TEST_TIME_COMPLEXITY || FORWARD_WITH_PURE_ROUTE_TABLE)
						{

						}
						else
						{

							if (addrsp->alias.networkType == NETWORK_IPV6)
							{
								Ipv6UpdateForwardingTable(
									node,
									GetIPv6Address(addrsp->alias),
									128,
									GetIPv6Address(link->neighbor_iface_addr),
									new_route_entry->rt_interface,
									new_route_entry->rt_metric,
									ROUTING_PROTOCOL_OLSR_INRIA);
							}
							else
							{

								if (_OLSR_MULTIPATH)
								{

									OLSRv1UpdateForwardingTableWithDisjointPath(node, new_route_entry);
								}
								else
								{

									NetworkUpdateForwardingTable(
										node,
										GetIPv4Address(addrsp->alias),
										0xffffffff,
										GetIPv4Address(link->neighbor_iface_addr),
										new_route_entry->rt_interface,
										new_route_entry->rt_metric,
										ROUTING_PROTOCOL_OLSR_INRIA);
								}                  
							}

						}

                       
						if (new_route_entry != NULL)
                        {
                            destination_n* list_destination_tmp;
                            list_destination_tmp = (destination_n* )
                                MEM_malloc(sizeof(destination_n));

                            memset(
                                list_destination_tmp,
                                0,
                                sizeof(destination_n));

                            list_destination_tmp->destination =
                                new_route_entry;
                            
							//list_destination_tmp->next = list_destination_n;
                            //list_destination_n = list_destination_tmp;

							if (list_destination_n == NULL)
							{
								list_destination_n = list_destination_tmp;
								tmp_destination_tail = list_destination_tmp;
							}
							else
							{
								//list_destination_tmp->next = NULL;
								//list_destination_tmp->next = ;

								//list_destination_n->next = list_destination_tmp;
								tmp_destination_tail->next = list_destination_tmp;
								tmp_destination_tail = tmp_destination_tail->next;

							}

                        }
                    }

                    addrsp = addrsp->next_alias;
                }

                neigh_2_list = neigh_2_list->neighbor_2_next;
            }
        }
    }

	if (_TEST_TIME_COMPLEXITY && uiLookupCntFor2Hop != NULL)
	{

		*uiLookupCntFor2Hop = uiCnt;

	}
	

    return list_destination_n;
}


static
destination_n* OlsrFillRoutingTableWith2HopNeighborsForSpecificNeighbor(
    Node* node, NodeAddress naNeighbor, UInt32 * uiLookupCntFor2Hop = NULL)
{


	UInt32 uiCnt = 0;

    destination_n* list_destination_n = NULL;

	destination_n* tmp_destination_tail = NULL;

    unsigned char index;
    neighbor_entry* neighbor;
    neighborhash_type* hash_neighbor;

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    //for (index = 0; index < HASHSIZE; index++)
    {
        hash_neighbor = &olsr->neighbortable.neighborhash[naNeighbor % HASHMASK];

        for (neighbor = hash_neighbor->neighbor_forw;
            neighbor != (neighbor_entry *) hash_neighbor;
            neighbor = neighbor->neighbor_forw)
        {
            neighbor_2_list_entry* neigh_2_list;

            if (neighbor->neighbor_status != SYM)
            {
                continue;
            }

			if (neighbor->neighbor_main_addr.interfaceAddr.ipv4 == naNeighbor)
			{
				//return neighbor;
				//continue
				neigh_2_list = neighbor->neighbor_2_list;
				while (neigh_2_list != NULL)
				{
					Address n2_addr;
					mid_address addrs;
					memset( &addrs, 0, sizeof(mid_address));
					mid_address* addrsp;

					n2_addr = neigh_2_list->neighbor_2->neighbor_2_addr;

					if (DEBUG)
					{
						char addrString[MAX_STRING_LENGTH];
						IO_ConvertIpAddressToString(&n2_addr,
								addrString);

						printf("Checking Node  %s\n",
								addrString);
					}

	                
					// Peter Modified to support multipath
					//rt_entry* tr_tmp = NULL;
					RouteEntryType ret = NOT_ALLOWED;

					double dDistance = 0.0;
					double dRWON = 0.0;


					if (_OLSR_MULTIPATH)
					{
						if (_TEST_TIME_COMPLEXITY)
						{
							dRWON = neighbor->neighbor_infos.dDegreeWRTNode;
							dDistance = neighbor->neighbor_infos.dDistanceWRTNode;
						}
						else
						{
							dRWON = ComputeRouterDegreeWRTOriginNode(node, neighbor->neighbor_main_addr.interfaceAddr.ipv4, &dDistance);
							dRWON = SimulateLocalDirectionOfAoA(node, dRWON);

						}
					}					

									
					
					if (_TEST_TIME_COMPLEXITY && uiLookupCntFor2Hop != NULL)
					{						
						uiCnt++;


						/*
						if (uiCnt > 5)
						{
							printf("uiCnt = %d \n", uiCnt);

						}
						*/
						
					}
					

					rt_entry* rt_tmp = NULL;
					if (_OLSR_MULTIPATH)
					{
									
						ret = OlsrAdvancedLookupRoutingTable(node, n2_addr, neighbor->neighbor_main_addr, 2, 
													dRWON, 
													_OLSR_TEMP_ROUTES_LIMIT, neighbor->neighbor_main_addr);
						if (ret == NOT_ALLOWED)
						{
							neigh_2_list = neigh_2_list->neighbor_2_next;
							continue;
						}
					}
					else
					{
						//rt_entry* rt_tmp = NULL; 
						rt_tmp = OlsrLookupRoutingTable(node, n2_addr);
						if (rt_tmp != NULL)
						{

							if (rt_tmp->rt_entry_infos.rtu_metric > 2)
							{
								//if exist one is larger, then still add this new
								//OlsrDeleteRoutingTable(rt_tmp);
							}
							else
							{

								if (g_iToAchieveSameRoute == 1)
								{
									if (rt_tmp->rt_entry_infos.rtu_metric == 2 && PreferredRouteForNew(naNeighbor, rt_tmp->rt_entry_infos.rtu_router.interfaceAddr.ipv4))
									{

										//OlsrDeleteRoutingTable(rt_tmp);										
									}
									else
									{
										neigh_2_list = neigh_2_list->neighbor_2_next;
										continue;
									}
									
								}
								else
								{
									neigh_2_list = neigh_2_list->neighbor_2_next;
									continue;
								}	

							}
							
						}

					}


					if (!OlsrIs2HopNeighborReachable(neigh_2_list))
					{
						neigh_2_list = neigh_2_list->neighbor_2_next;
						continue;
					}

					addrs.alias = n2_addr;
					addrs.next_alias = OlsrLookupMidAliases(node,n2_addr);
					addrsp = &addrs;

					while (addrsp!=NULL)
					{
						link_entry* link = OlsrGetBestLinktoNeighbor(
											   node,
											   neighbor->neighbor_main_addr);

						if (link)
						{
							// Peter modified to support multipath						
							
							rt_entry* new_route_entry = NULL;

							if (rt_tmp != NULL)
							{
								new_route_entry = rt_tmp;
							}
							else
							{
								new_route_entry = OlsrInsertRoutingTable(node, addrsp->alias);
							}

							
							new_route_entry->rt_router =
								link->neighbor_iface_addr;

							new_route_entry->rt_entry_infos.rtu_lasthop = link->neighbor_iface_addr;


							if (_OLSR_MULTIPATH)
							{
								if (_TEST_TIME_COMPLEXITY)
								{
									new_route_entry->rt_entry_infos.related_neighbor = neighbor;					

								}
								else
								{
									new_route_entry->rt_entry_infos.rtu_DegreeWRTNode = dRWON;

									new_route_entry->rt_entry_infos.rtu_DistanceWRTNode = dDistance;

								}
							}
														
	                                                
							// The next router is the neighbor itself
							new_route_entry->rt_metric = 2;

							new_route_entry->rt_interface =
								 RoutingOlsrCheckMyIfaceAddress(
									node,
									link->local_iface_addr);

							if (DEBUG)
							{
								char addrString1[MAX_STRING_LENGTH];
								char addrString2[MAX_STRING_LENGTH];
								IO_ConvertIpAddressToString(&addrsp->alias,
									addrString1);
								IO_ConvertIpAddressToString(
									&link->neighbor_iface_addr,
									addrString2);
								printf("Updating Routing Table at node %d\n",
									node->nodeId);
								printf("Dst : %s Next Hop : %s Interface: %d"
									" Metric: %d\n",
									addrString1,
									addrString2,
									new_route_entry->rt_interface,
									new_route_entry->rt_metric);
							}

							if (_TEST_TIME_COMPLEXITY || FORWARD_WITH_PURE_ROUTE_TABLE)
							{

							}
							else
							{

								if (addrsp->alias.networkType == NETWORK_IPV6)
								{
									Ipv6UpdateForwardingTable(
										node,
										GetIPv6Address(addrsp->alias),
										128,
										GetIPv6Address(link->neighbor_iface_addr),
										new_route_entry->rt_interface,
										new_route_entry->rt_metric,
										ROUTING_PROTOCOL_OLSR_INRIA);
								}
								else
								{

									if (_OLSR_MULTIPATH)
									{

										OLSRv1UpdateForwardingTableWithDisjointPath(node, new_route_entry);
									}
									else
									{

										NetworkUpdateForwardingTable(
											node,
											GetIPv4Address(addrsp->alias),
											0xffffffff,
											GetIPv4Address(link->neighbor_iface_addr),
											new_route_entry->rt_interface,
											new_route_entry->rt_metric,
											ROUTING_PROTOCOL_OLSR_INRIA);
									}                  
								}

							}

	                       
							if (new_route_entry != NULL)
							{
								destination_n* list_destination_tmp;
								list_destination_tmp = (destination_n* )
									MEM_malloc(sizeof(destination_n));

								memset(
									list_destination_tmp,
									0,
									sizeof(destination_n));

								list_destination_tmp->destination =
									new_route_entry;
								
								//list_destination_tmp->next = list_destination_n;
								//list_destination_n = list_destination_tmp;

								
								if (list_destination_n == NULL)
								{
									list_destination_n = list_destination_tmp;
									tmp_destination_tail = list_destination_tmp;
								}
								else
								{
									//list_destination_tmp->next = NULL;
									//list_destination_tmp->next = ;
									
									//list_destination_n->next = list_destination_tmp;
									tmp_destination_tail->next = list_destination_tmp;
									tmp_destination_tail = tmp_destination_tail->next;

								}
								
							}
						}

						addrsp = addrsp->next_alias;
					}

					neigh_2_list = neigh_2_list->neighbor_2_next;
				}
				
			
				break;
			}

            
        }
    }

	if (_TEST_TIME_COMPLEXITY && uiLookupCntFor2Hop != NULL)
	{

		*uiLookupCntFor2Hop = uiCnt;

	}
	

    return list_destination_n;
}


// /**
// FUNCTION   :: OlsrFillRoutingTableWithNeighbors
// LAYER      :: APPLICATION
// PURPOSE    :: Fills routing table with 1 hop neighbors
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// RETURN :: Int32 :  1
// **/

static
Int32 OlsrFillRoutingTableWithNeighbors(Node *node, BOOL bForCompare = FALSE)
{
    int index;
    neighbor_entry* neighbor;
    neighborhash_type* hash_neighbor;
    rt_entry* new_route_entry = NULL;

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    for (index = 0; index < HASHSIZE; index++)
    {
        hash_neighbor = &olsr->neighbortable.neighborhash[index];

        for (neighbor = hash_neighbor->neighbor_forw;
            neighbor != (neighbor_entry *) hash_neighbor;
            neighbor = neighbor->neighbor_forw)
        {
            if (neighbor->neighbor_status == SYM)
            {
                mid_address  addrs;
                memset( &addrs, 0, sizeof(mid_address));
                mid_address* addrs2;

                if (DEBUG)
                {
                    OlsrPrintMidTable(node);
                }
                addrs.alias = neighbor->neighbor_main_addr;
                addrs.next_alias = OlsrLookupMidAliases(
                                       node,
                                       neighbor->neighbor_main_addr);

                addrs2 = &addrs;

                if (DEBUG)
                {
                    printf(" List of aliases to be added\n");
                    mid_address* tmp_addr;
                    tmp_addr = &addrs;

                    while (tmp_addr != NULL)
                    {
                        char addrString[MAX_STRING_LENGTH];
                        IO_ConvertIpAddressToString(&tmp_addr->alias,
                                    addrString);
                        printf(" Alias: %s\n", addrString);

                        tmp_addr = tmp_addr->next_alias;
                    }
                }

                while (addrs2 != NULL)
                {
                    link_entry* link = OlsrGetBestLinktoNeighbor(
                                           node, addrs2->alias);

                    if (link)
                    {
                        // inserts each neighbor in the routing table
                        new_route_entry = OlsrInsertRoutingTable(
                                              node,
                                              addrs2->alias, bForCompare);

                        new_route_entry->rt_router =
                            link->neighbor_iface_addr;

						SetIPv4AddressInfo(&new_route_entry->rt_entry_infos.rtu_lasthop, node->nodeId);

						
						if (_OLSR_MULTIPATH)
						{
							if (_TEST_TIME_COMPLEXITY)
							{
								new_route_entry->rt_entry_infos.related_neighbor = neighbor;
							}
							else
							{


								{
									double dDistance = 0.0;
									double dRWON = ComputeRouterDegreeWRTOriginNode(node, link->neighbor_iface_addr.interfaceAddr.ipv4, &dDistance);

									new_route_entry->rt_entry_infos.rtu_DegreeWRTNode = SimulateLocalDirectionOfAoA(node, dRWON);
									new_route_entry->rt_entry_infos.rtu_DistanceWRTNode = dDistance;
								}							   
							}
						}
						

                        // The next router is the neighbor itself
                        new_route_entry->rt_metric = 1;

                        new_route_entry->rt_interface =
                            RoutingOlsrCheckMyIfaceAddress(
                                node,
                                link->local_iface_addr);

                        if (DEBUG)
                        {
                            char addrString1[MAX_STRING_LENGTH];
                            char addrString2[MAX_STRING_LENGTH];
                            IO_ConvertIpAddressToString(
                                &addrs2->alias,
                                addrString1);
                            IO_ConvertIpAddressToString(
                                &link->neighbor_iface_addr,
                                addrString2);
                            printf("Updating Routing Table at node %d\n",
                                node->nodeId);
                            printf("Dst : %s Next Hop : %s Interface: %d"
                                " Metric: %d\n",
                                 addrString1, addrString2,
                                 new_route_entry->rt_interface,
                                 new_route_entry->rt_metric);
                        }


						if (_TEST_TIME_COMPLEXITY || FORWARD_WITH_PURE_ROUTE_TABLE)
						{

						}
						else
						{
							if (addrs2->alias.networkType == NETWORK_IPV6)
							{
								Ipv6UpdateForwardingTable(
									node,
									GetIPv6Address(addrs2->alias),
									128,
									GetIPv6Address(link->neighbor_iface_addr),
									new_route_entry->rt_interface,
									new_route_entry->rt_metric,
									ROUTING_PROTOCOL_OLSR_INRIA);
							}
							else
							{
								if (_OLSR_MULTIPATH)
								{

									OLSRv1UpdateForwardingTableWithDisjointPath(node, new_route_entry);
								}
								else
								{
									NetworkUpdateForwardingTable(
										node,
										GetIPv4Address(addrs2->alias),
										0xffffffff,
										GetIPv4Address(link->neighbor_iface_addr),
										new_route_entry->rt_interface,
										new_route_entry->rt_metric,
										ROUTING_PROTOCOL_OLSR_INRIA);
								}							

							}




						}

                        
                    }
                    addrs2 = addrs2->next_alias;
                }
            }
        }
    }
    return 1 ;
}


static
Int32 OlsrFillRoutingTableWithSpecificNeighbor(Node *node, NodeAddress naNeighbor)
{
	int index;
	neighbor_entry* neighbor;
	neighborhash_type* hash_neighbor;
	rt_entry* new_route_entry = NULL;

	RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

	//for (index = 0; index < HASHSIZE; index++)
	{
		hash_neighbor = &olsr->neighbortable.neighborhash[naNeighbor % HASHMASK];

		for (neighbor = hash_neighbor->neighbor_forw;
			neighbor != (neighbor_entry *) hash_neighbor;
			neighbor = neighbor->neighbor_forw)
		{
			if (neighbor->neighbor_status == SYM && neighbor->neighbor_main_addr.interfaceAddr.ipv4 == naNeighbor)
			{
				mid_address  addrs;
				memset( &addrs, 0, sizeof(mid_address));
				mid_address* addrs2;

				if (DEBUG)
				{
					OlsrPrintMidTable(node);
				}
				addrs.alias = neighbor->neighbor_main_addr;
				addrs.next_alias = OlsrLookupMidAliases(
					node,
					neighbor->neighbor_main_addr);

				addrs2 = &addrs;

				if (DEBUG)
				{
					printf(" List of aliases to be added\n");
					mid_address* tmp_addr;
					tmp_addr = &addrs;

					while (tmp_addr != NULL)
					{
						char addrString[MAX_STRING_LENGTH];
						IO_ConvertIpAddressToString(&tmp_addr->alias,
							addrString);
						printf(" Alias: %s\n", addrString);

						tmp_addr = tmp_addr->next_alias;
					}
				}

				while (addrs2 != NULL)
				{
					link_entry* link = OlsrGetBestLinktoNeighbor(
						node, addrs2->alias);

					if (link)
					{


						rt_entry* rt_tmp = OlsrLookupRoutingTable(node, neighbor->neighbor_main_addr);

						if (rt_tmp != NULL && rt_tmp->rt_entry_infos.rtu_metric > 1)
						{

							//OlsrDeleteRoutingTable(rt_tmp);
							new_route_entry = rt_tmp;
						}
						else
						{
							// inserts each neighbor in the routing table
							new_route_entry = OlsrInsertRoutingTable(
								node,
								addrs2->alias);
						}

						
						new_route_entry->rt_router =
							link->neighbor_iface_addr;

						SetIPv4AddressInfo(&new_route_entry->rt_entry_infos.rtu_lasthop, node->nodeId);

						if (_OLSR_MULTIPATH)
						{
							if (_TEST_TIME_COMPLEXITY)
							{
								new_route_entry->rt_entry_infos.related_neighbor = neighbor;
							}
							else
							{


								{
									double dDistance = 0.0;
									double dRWON = ComputeRouterDegreeWRTOriginNode(node, link->neighbor_iface_addr.interfaceAddr.ipv4, &dDistance);

									new_route_entry->rt_entry_infos.rtu_DegreeWRTNode = SimulateLocalDirectionOfAoA(node, dRWON);
									new_route_entry->rt_entry_infos.rtu_DistanceWRTNode = dDistance;
								}							
							}
						}
						

						// The next router is the neighbor itself
						new_route_entry->rt_metric = 1;

						new_route_entry->rt_interface =
							RoutingOlsrCheckMyIfaceAddress(
							node,
							link->local_iface_addr);

						if (DEBUG)
						{
							char addrString1[MAX_STRING_LENGTH];
							char addrString2[MAX_STRING_LENGTH];
							IO_ConvertIpAddressToString(
								&addrs2->alias,
								addrString1);
							IO_ConvertIpAddressToString(
								&link->neighbor_iface_addr,
								addrString2);
							printf("Updating Routing Table at node %d\n",
								node->nodeId);
							printf("Dst : %s Next Hop : %s Interface: %d"
								" Metric: %d\n",
								addrString1, addrString2,
								new_route_entry->rt_interface,
								new_route_entry->rt_metric);
						}


						if (_TEST_TIME_COMPLEXITY || FORWARD_WITH_PURE_ROUTE_TABLE)
						{

						}
						else
						{
							if (addrs2->alias.networkType == NETWORK_IPV6)
							{
								Ipv6UpdateForwardingTable(
									node,
									GetIPv6Address(addrs2->alias),
									128,
									GetIPv6Address(link->neighbor_iface_addr),
									new_route_entry->rt_interface,
									new_route_entry->rt_metric,
									ROUTING_PROTOCOL_OLSR_INRIA);
							}
							else
							{
								if (_OLSR_MULTIPATH)
								{

									OLSRv1UpdateForwardingTableWithDisjointPath(node, new_route_entry);
								}
								else
								{
									NetworkUpdateForwardingTable(
										node,
										GetIPv4Address(addrs2->alias),
										0xffffffff,
										GetIPv4Address(link->neighbor_iface_addr),
										new_route_entry->rt_interface,
										new_route_entry->rt_metric,
										ROUTING_PROTOCOL_OLSR_INRIA);
								}							

							}

						}

					}
					addrs2 = addrs2->next_alias;
				}

				break;
			}
		}
	}
	return 1 ;
}


// /**
// FUNCTION   :: OlsrInsertRoutingTableFromHnaTable
// LAYER      :: APPLICATION
// PURPOSE    :: Fills routing table from HNA table
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// RETURN :: void :  NULL
// **/

static
void OlsrInsertRoutingTableFromHnaTable(Node* node)
{
    //Peter comment: this function although called, will not update forwarding table in current scnario.
	
	
    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;
    hna_entry* tmp_hna;
    hna_net* tmp_net;
    rt_entry *tmp_rt, *route_entry;

    unsigned char index;
    for (index = 0; index < HASHSIZE; index++)
    {
        // ALL hna entry
        for (tmp_hna = olsr->hna_table[index].next;
            tmp_hna != &olsr->hna_table[index];
            tmp_hna = tmp_hna->next)
        {
            // All networks
            for (tmp_net = tmp_hna->networks.next;
                 tmp_net != &tmp_hna->networks;
                 tmp_net = tmp_net->next)
            {

                // If no route to gateway - skip
                if ((tmp_rt = OlsrLookupRoutingTable(node,
                                tmp_hna->A_gateway_addr)) == NULL)
                {
                   continue;
                }
                if ((route_entry = OlsrLookupRoutingTable(node,
                                tmp_net->A_network_addr)) != NULL)
                {
                    // If there exists a better or equal entry - skip
                    if (route_entry->rt_metric > tmp_rt->rt_metric + 1)
                    {
                        // Replace old route with this better one
                        route_entry->rt_router = tmp_rt->rt_router;
                        route_entry->rt_metric = (UInt16) (tmp_rt->rt_metric)
                                                 + 1;
                        route_entry->rt_interface = tmp_rt->rt_interface;
                    }
                    else
                    {
                        continue;
                    }
                }
                else
                {
                    // If not - create a new one and
                    // add into route table

                    route_entry = OlsrInsertRoutingTable(node,
                                      tmp_net->A_network_addr);
                    route_entry->rt_router = tmp_rt->rt_router;
                    route_entry->rt_metric = (UInt16) (tmp_rt->rt_metric)
                                             + 1;
                    route_entry->rt_interface = tmp_rt->rt_interface;
                }

                if (DEBUG)
                {
                    char addrString1[MAX_STRING_LENGTH];
                    char addrString2[MAX_STRING_LENGTH];

                    IO_ConvertIpAddressToString(&tmp_net->A_network_addr,
                        addrString1);
                    IO_ConvertIpAddressToString(&route_entry->rt_router,
                        addrString2);

                    printf("Updating Routing Table at node %d\n",node->nodeId);
                    printf("Dst: %s Next Hop: %s Interface: %d Metric: %d\n",
                        addrString1,
                        addrString2,
                        route_entry->rt_interface,
                        route_entry->rt_metric);
                }

              if (tmp_net->A_network_addr.networkType == NETWORK_IPV6)
              {
                    in6_addr ipv6_addr_prefix;
                    in6_addr ipv6_addr = GetIPv6Address(
                                             tmp_net->A_network_addr);
                    Ipv6GetPrefix(&ipv6_addr,
                        &ipv6_addr_prefix, tmp_net->A_netmask.v6);

                    Ipv6UpdateForwardingTable(
                        node,
                        ipv6_addr_prefix,
                        tmp_net->A_netmask.v6,
                        GetIPv6Address(route_entry->rt_router),
                        route_entry->rt_interface,
                        route_entry->rt_metric,
                        ROUTING_PROTOCOL_OLSR_INRIA);
              }
              else

              {
                    if (tmp_net->A_netmask.v4)
                    {
                        NetworkUpdateForwardingTable(
                                node,
                                GetIPv4Address(tmp_net->A_network_addr)
                                    % tmp_net->A_netmask.v4,
                                tmp_net->A_netmask.v4,
                                GetIPv4Address(route_entry->rt_router),
                                route_entry->rt_interface,
                                route_entry->rt_metric,
                                ROUTING_PROTOCOL_OLSR_INRIA);
                    }
                    else
                    {
                        NetworkUpdateForwardingTable(
                                node,
                                GetIPv4Address(tmp_net->A_network_addr),
                                tmp_net->A_netmask.v4,
                                GetIPv4Address(route_entry->rt_router),
                                route_entry->rt_interface,
                                route_entry->rt_metric,
                                ROUTING_PROTOCOL_OLSR_INRIA);
                    }

              }
          }
       }
   }
}

// /**
// FUNCTION   :: OlsrRoutingMirror
// LAYER      :: APPLICATION
// PURPOSE    :: Make mirror of current routing table
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// RETURN :: void : NULL
// **/

static
void OlsrRoutingMirror(
    Node* node)
{
    Int32 index;
    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    for (index = 0; index < HASHSIZE; index++)
    {
        if (olsr->routingtable[index].rt_forw ==
            (rt_entry *) &olsr->routingtable[index])
        {
            olsr->mirror_table[index].rt_forw = (rt_entry *)
                    &olsr->mirror_table[index];

            olsr->mirror_table[index].rt_back = (rt_entry *)
                    &olsr->mirror_table[index];
        }
        else
        {
            olsr->mirror_table[index].rt_forw =
                    olsr->routingtable[index].rt_forw;

            olsr->mirror_table[index].rt_forw->rt_back =
                    (rt_entry *) &olsr->mirror_table[index];

            olsr->mirror_table[index].rt_back =
                    olsr->routingtable[index].rt_back;

            olsr->mirror_table[index].rt_back->rt_forw =
                    (rt_entry *) &olsr->mirror_table[index];

            olsr->routingtable[index].rt_forw =
                    (rt_entry *) &olsr->routingtable[index];

            olsr->routingtable[index].rt_back =
                    (rt_entry *) &olsr->routingtable[index];
        }
    }
}

// /**
// FUNCTION   :: OlsrPrintRoutingTable
// LAYER      :: APPLICATION
// PURPOSE    :: Prints routing table
// PARAMETERS ::
// + table : rthash* : Pointer to Table to be printed
// RETURN :: void : NULL
// **/


void PrintRoutingTableForAEntry(rt_entry* destination, char * pszRT = NULL, BOOL bShowFull = TRUE)
{

	
	char addrString1[MAX_STRING_LENGTH];
    char addrString2[MAX_STRING_LENGTH];

	//Peter Modified to support disjoint path
	//_OLSR_DISJOINTPATH
	char addrString3[MAX_STRING_LENGTH] = {0};
	char addrString4[MAX_STRING_LENGTH] = {0};

	char buf[MAX_STRING_LENGTH] = {0};

    IO_ConvertIpAddressToString(&destination->rt_dst,
                                addrString1);

    IO_ConvertIpAddressToString(&destination->rt_router,
                                addrString2);


	IO_ConvertIpAddressToString(&destination->rt_entry_infos.rtu_lasthop,
								addrString3);

	/*
	if (destination->rt_entry_infos.rtu_recommended_2hop.networkType != NETWORK_INVALID)
	{

		IO_ConvertIpAddressToString(&destination->rt_entry_infos.rtu_recommended_2hop,
			addrString3);

	}	

	for (int i = 0; i < _OLSR_DISJOINTPATH_UNRECOMENDED_LIMIT; i++)
	{

		if (destination->rt_entry_infos.rtu_unrecommended_2hop[i].networkType != NETWORK_INVALID)
		{

			IO_ConvertIpAddressToString(&destination->rt_entry_infos.rtu_unrecommended_2hop[i],
				addrString4);

			sprintf(buf, "%s  %s", buf, addrString4);

		}
	}
	*/
	
	

	/*
    printf("%-15s %-15s  %-15s  %-15s        %-10d   %-10d\n",addrString1,
            addrString2, addrString3, buf, destination->rt_interface,
                    destination->rt_metric);
	*/


    double dDgrWRT = 0.0;
    double dDtsWRT = 0.0; 


	if (_OLSR_MULTIPATH)
	{
		if (_TEST_TIME_COMPLEXITY)
		{
			dDgrWRT = destination->rt_entry_infos.related_neighbor->neighbor_infos.dDegreeWRTNode;
			dDtsWRT = destination->rt_entry_infos.related_neighbor->neighbor_infos.dDistanceWRTNode;
		}
		else
		{
			dDgrWRT = destination->rt_entry_infos.rtu_DegreeWRTNode;
			dDtsWRT = destination->rt_entry_infos.rtu_DistanceWRTNode;
		}
	}

       



	if (g_iRunTimeCompare == 1)
	{
		if (pszRT == NULL)
		{
			return;
		}

		if (bShowFull)
		{

			sprintf(pszRT, "%s%-15s %-15s  %-15s   %-10d   %-10d   \n", pszRT, addrString1, 
				addrString2, addrString3, destination->rt_interface, destination->rt_metric);
		}
		else
		{
			if (g_iToAchieveSameRoute == 1)
			{

				sprintf(pszRT, "%s%-15s %-15s    %-10d   \n", pszRT, addrString1, addrString2, destination->rt_metric);
			}
			else
			{

				sprintf(pszRT, "%s%-15s    %-10d   \n", pszRT, addrString1, destination->rt_metric);
			}
		}

	}
	else
	{
		if (g_iChaseRouteTable == 1)
		{

			if (g_iChaseRouteTableSkipRouteLast == 1)
			{
				

				if (g_iToAchieveSameRoute == 1)
				{

					sprintf(g_szTextRT, "%s%-15s %-15s  %-15s   %-10d   %-10d   %-10f   %-10f \n", g_szTextRT, addrString1,
						addrString2, "0.0.0.0", destination->rt_interface, destination->rt_metric, 
						0.0, 
						0.0);
				}
				else
				{

					sprintf(g_szTextRT, "%s%-15s %-15s  %-15s   %-10d   %-10d   %-10f   %-10f \n", g_szTextRT, addrString1,
						"0.0.0.0", "0.0.0.0", destination->rt_interface, destination->rt_metric, 
						0.0, 
						0.0);
				}

				/*
				sprintf(g_szTextRT, "%s%-15s %-15s  %-15s   %-10d   %-10d   %-10f   %-10f \n", g_szTextRT, addrString1,
					"0.0.0.0", "0.0.0.0", destination->rt_interface, destination->rt_metric, 
					0, 
					0);
				*/
				
									
				
				
				
			}
			else
			{
				

				sprintf(g_szTextRT, "%s%-15s %-15s  %-15s   %-10d   %-10d   %-10f   %-10f \n", g_szTextRT, addrString1,
					addrString2, addrString3, destination->rt_interface, destination->rt_metric, 
					0.0, 
					0.0);
			}

			

		}
		else
		{

			printf("%-15s %-15s  %-15s   %-10d   %-10d   %-10f   %-10f \n",addrString1,
				addrString2, addrString3, destination->rt_interface, destination->rt_metric, 
				dDgrWRT, 
				dDtsWRT);

		}
	}


	


}

static
void OlsrPrintRoutingTable(
    rthash* table, char * pszRT = NULL, BOOL bShowFull = TRUE)
{
    rt_entry* destination;
    rthash* routing_hash;
    int index;


	if (g_iRunTimeCompare == 1)
	{
		if (pszRT == NULL)
		{
			return;
		}

		sprintf(pszRT, "Routing Table:\n");
		
		if (bShowFull)
		{
			sprintf(pszRT, "%sDest             NextHop        LastHop          Intf       Distance \n", pszRT);
		}
		else
		{
			if (g_iToAchieveSameRoute == 1)
			{
				sprintf(pszRT, "%sDest             NextHop           Distance \n", pszRT);
			}
			else
			{
				sprintf(pszRT, "%sDest       Distance \n", pszRT);
			}
		}
		
	}
	else
	{

		if (g_iChaseRouteTable == 1)
		{
			memset(g_szTextRT, 0, 16384 * sizeof(char));

			sprintf(g_szTextRT, "Routing Table:\n");
			sprintf(g_szTextRT, "%sDest             NextHop        LastHop          Intf       Distance \n", g_szTextRT);

		}
		else
		{
			printf("Routing Table:\n");
			//printf("Dest            NextHop     Positive_Next2Hop   Negative_Next2Hop1  Negative_Next2Hop2  Negative_Next2Hop3  Negative_Next2Hop4  Negative_Next2Hop5     Intf     Distance\n");

			printf("Dest             NextHop        LastHop          Intf       Distance \n");
		}
	}
	
    
    for (index = 0; index < HASHSIZE; index++)
    {

		// insert in routing table using topology
		destination_n* destination_n_of_current_hash = NULL;

	
        routing_hash = &table[index];
        for (destination = routing_hash->rt_forw;
            destination != (rt_entry *) routing_hash;
            destination = destination->rt_forw)
        {
           
			
			if (g_iRunTimeCompare == 1 || g_iChaseRouteTable == 1)
			{

				destination_n* destination_n_1 = (destination_n *)
				MEM_malloc(sizeof(destination_n));

				memset(destination_n_1, 0, sizeof(destination_n));

				destination_n_1->destination = destination;

				if (destination_n_of_current_hash == NULL)
				{
					destination_n_of_current_hash = destination_n_1;
					//*p_tmp_destination_tail = destination_n_1;
				}
				else
				{
					
					if (destination_n_of_current_hash->destination->rt_entry_infos.rtu_hash < destination_n_1->destination->rt_entry_infos.rtu_hash)
					{
						//keep on search until find right position
						destination_n* p_tmp_destination = destination_n_of_current_hash;
						while (p_tmp_destination->next != NULL)
						{
							
							if (p_tmp_destination->next->destination->rt_entry_infos.rtu_hash < destination_n_1->destination->rt_entry_infos.rtu_hash)
							{
								
							}
							else
							{
	
								break;
							}

							p_tmp_destination = p_tmp_destination->next;
						}

						//insert after the recent p_tmp_destination
						destination_n_1->next = p_tmp_destination->next;
						p_tmp_destination->next = destination_n_1;


					}
					else
					{
						//insert before the destination_n_of_current_hash
						destination_n_1->next = destination_n_of_current_hash;

						destination_n_of_current_hash = destination_n_1;
					}
					
				}

			}
			else			
			{
				PrintRoutingTableForAEntry(destination, pszRT, bShowFull);
			}		
		}

		if (g_iRunTimeCompare == 1 || g_iChaseRouteTable == 1)
		{

		
			while (destination_n_of_current_hash != NULL)
			{

				PrintRoutingTableForAEntry(destination_n_of_current_hash->destination, pszRT, bShowFull);
				
				destination_n* tmp_desn = destination_n_of_current_hash;
				destination_n_of_current_hash = destination_n_of_current_hash->next;

				MEM_free(tmp_desn);
			}
		}		
		
    }
}



//Peter Modified for disjoint path
//_OLSR_DISJOINTPATH

/*
static
void GenerateRecommendedOrUnrecommended2Hops(Node *node, rt_entry* rt_first, rt_entry* rt_bound)
{


	Int32 index2;
	neighbor_2_entry* neighbor_2;
	neighbor2_hash* hash_2_neighbor;
	rt_entry* destination;

	RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

	
	UInt16 iUnrecommendedCnt = 0;

	for (index2 = 0; index2 < HASHSIZE; index2++)
	{
		
		if (iUnrecommendedCnt == _OLSR_DISJOINTPATH_UNRECOMENDED_LIMIT)
		{

			break;
		}
		
		hash_2_neighbor = &olsr->neighbor2table[index2];

		for (neighbor_2 = hash_2_neighbor->neighbor2_forw;
			neighbor_2 != (neighbor_2_entry *) hash_2_neighbor;
			neighbor_2 = neighbor_2->neighbor_2_forw)
		{

			if (iUnrecommendedCnt == _OLSR_DISJOINTPATH_UNRECOMENDED_LIMIT)
			{

				break;
			}

			UInt32 hash;
			rthash* routing_hash;
			

			OlsrHashing(neighbor_2->neighbor_2_addr, &hash);
			

			RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;
			routing_hash = &olsr->routingtable[hash % HASHMASK];

			bool bSkip = false;

			UInt16 min_cost = 0;
			
			for (destination = routing_hash->rt_forw;
				destination != (rt_entry* ) routing_hash;
				destination = destination->rt_forw)
			{

				if (destination->rt_hash != hash)
				{

					if (bSkip)
					{
					
						break;
					}
					else
					{

						continue;
					}
					
				}
				else
				{

					bSkip = true;
					
					if(min_cost == 0)
					{
					
						min_cost = destination->rt_metric;
					}
					else
					{

						if (destination->rt_metric < min_cost)
						{

							min_cost = destination->rt_metric;
						}
					}

				}


				//
				//Peter comment: assume that every route has the same shortest cost based 
				//on modified route discovery algorithm
				//if (destination->rt_metric != 2)   //2 means exactly two hop away
				//{
					
				//	bSkip = true;
				//}

				//break;
				//
			}

			if (min_cost != 2)
			{
				//to consider the next 2 hop neighbor
				continue;
			}			
			
						
			
			int iNeighborMatchCnt = 0;
			int iNeighborCnt = 0;
			rt_entry* rte_tmp = NULL;


			neighbor_list_entry* list_1 = NULL;

			list_1 = neighbor_2->neighbor_2_nblist;

			while (list_1 != NULL)
			{
				iNeighborCnt++;
				
				for (destination = rt_first;
					destination != rt_bound;
					destination = destination->rt_forw)
				{

				
					if (Address_IsSameAddress(&list_1->neighbor->neighbor_main_addr, &destination->rt_router))
					{

						if (iNeighborMatchCnt >= 1)
						{

							rte_tmp->rt_entry_infos.rtu_unrecommended_2hop[iUnrecommendedCnt] = neighbor_2->neighbor_2_addr;

							OLSRv1UpdateForwardingTableWithDisjointPath(node, rte_tmp);
							
						}

						rte_tmp = destination;

						iNeighborMatchCnt++;

					}

				}


				list_1 = list_1->neighbor_next;
			}


			if (iNeighborMatchCnt > 1)
			{

				rte_tmp->rt_entry_infos.rtu_unrecommended_2hop[iUnrecommendedCnt] = neighbor_2->neighbor_2_addr;

				OLSRv1UpdateForwardingTableWithDisjointPath(node, rte_tmp);

				iUnrecommendedCnt++;

			}
			else if (iNeighborMatchCnt == 1)
			{

				//consider the one who has only one neighbor that can only reached by this route 
				//(so the route is the only neighbor, since for other 2 hops node even if we do not 
				//set the recommended, it still can be choosed if no unrecommended exist.)  
				//if (iNeighborCnt == 1)
				//{


					rte_tmp->rt_entry_infos.rtu_recommended_2hop = neighbor_2->neighbor_2_addr;

					OLSRv1UpdateForwardingTableWithDisjointPath(node, rte_tmp);
				//}
				
			}
			else
			{

			}
	
		}			
	
	}
}
*/

//Peter Modified for disjoint path
//_OLSR_DISJOINTPATH

/*
static
void OptimizeRouteTable(Node *node, rthash* table)
{
	
	//Does not finished!!!!!!!!!!!   
	//Currently just copy from Generate2HopRoute
	
	//printf("Generate2HopRoute");
	rt_entry* destination;
	rthash* routing_hash;
	int index;


	for (index = 0; index < HASHSIZE; index++)
	{
		routing_hash = &table[index];

		int iRouteCnt = 0;

		UInt16 min_cost = 0;

		char addrString1[MAX_STRING_LENGTH];
		char addrString2[MAX_STRING_LENGTH];

		
		rt_entry* same_dst_first = NULL;
		rt_entry* same_dst_last = NULL;

		//Peter comment: the destinations with same hash values will included in same hash entries, 
		//so need to separate and deal with by sub-groups.

		for (destination = routing_hash->rt_forw;
			destination != (rt_entry *) routing_hash;
			destination = destination->rt_forw)
		{

			

			if (same_dst_first == NULL)
			{
				
				same_dst_first = destination;
			}


			if (same_dst_last != NULL)
			{
				
				//if (Address_IsSameAddress(&same_dst_last->rt_dst, &destination->rt_dst))
				if (same_dst_last->rt_hash == destination->rt_hash)
				{
				
					same_dst_last = destination;
				}
				else
				{
					
					//solve recommended and unrecommended
					if (same_dst_first != same_dst_last //more than one route
						&& min_cost >= DISJOINT_APPLY_THRESHOLD)  
					{

						GenerateRecommendedOrUnrecommended2Hops(node, same_dst_first, destination);

						// this destination is for the for loop in the sub function to meet a bound, 
						//which is the start of entry with different destination

					}

					min_cost = destination->rt_metric;

					same_dst_last = destination;
					same_dst_first = destination;
					
				}				
			}
			else
			{

				same_dst_last = destination;
			}


			if (min_cost == 0)
			{

				min_cost = destination->rt_metric;
			}
			else
			{
				if (destination->rt_metric < min_cost)
				{

					min_cost = destination->rt_metric;
				}				

			}

			  
		}


		if (same_dst_last != NULL)
		{

			//solve recommended and unrecommended for last sub-group with same destination
			if (same_dst_first != same_dst_last //more than one route
				&& min_cost >= DISJOINT_APPLY_THRESHOLD)  
			{

				GenerateRecommendedOrUnrecommended2Hops(node, same_dst_first, destination);

				// this destination is for the for loop in the sub function to meet a bound, 
				//which is the start of entry with different destination

			}			
			
		}
		
	}	
}
*/

/*
static
void Generate2HopRoute(Node *node, rthash* table)
{
	//printf("Generate2HopRoute");
	rt_entry* destination;
	rthash* routing_hash;
	int index;


	for (index = 0; index < HASHSIZE; index++)
	{
		routing_hash = &table[index];

		int iRouteCnt = 0;

		UInt16 min_cost = 0;

		char addrString1[MAX_STRING_LENGTH];
		char addrString2[MAX_STRING_LENGTH];

		
		rt_entry* same_dst_first = NULL;
		rt_entry* same_dst_last = NULL;

		//Peter comment: the destinations with same hash values will included in same hash entries, 
		//so need to separate and deal with by sub-groups.

		for (destination = routing_hash->rt_forw;
			destination != (rt_entry *) routing_hash;
			destination = destination->rt_forw)
		{

			
			

			if (same_dst_first == NULL)
			{
				
				same_dst_first = destination;
			}


			if (same_dst_last != NULL)
			{
				
				//if (Address_IsSameAddress(&same_dst_last->rt_dst, &destination->rt_dst))
				if (same_dst_last->rt_hash == destination->rt_hash)
				{
				
					same_dst_last = destination;
				}
				else
				{
					
					//solve recommended and unrecommended
					if (same_dst_first != same_dst_last //more than one route
						&& min_cost >= DISJOINT_APPLY_THRESHOLD)  
					{

						GenerateRecommendedOrUnrecommended2Hops(node, same_dst_first, destination);

						// this destination is for the for loop in the sub function to meet a bound, 
						//which is the start of entry with different destination

					}

					min_cost = destination->rt_metric;

					same_dst_last = destination;
					same_dst_first = destination;
					
				}				
			}
			else
			{

				same_dst_last = destination;
			}


			if (min_cost == 0)
			{

				min_cost = destination->rt_metric;
			}
			else
			{
				if (destination->rt_metric < min_cost)
				{

					min_cost = destination->rt_metric;
				}				

			}

			  
		}


		if (same_dst_last != NULL)
		{

			//solve recommended and unrecommended for last sub-group with same destination
			if (same_dst_first != same_dst_last //more than one route
				&& min_cost >= DISJOINT_APPLY_THRESHOLD)  
			{

				GenerateRecommendedOrUnrecommended2Hops(node, same_dst_first, destination);

				// this destination is for the for loop in the sub function to meet a bound, 
				//which is the start of entry with different destination

			}			
			
		}
		
	}	
}
*/


// /**
// FUNCTION   :: OlsrCalculateRoutingTable
// LAYER      :: APPLICATION
// PURPOSE    :: Calculate routing table
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// RETURN :: void : NULL
// **/

//Peter added to support real time query for _OLSR_MULTIPATH
#include "external_util.h"


static void OlsrCalculateRoutingTableForSinglePathTopologySearchHelpFuncForCompare(Node * node, Address addrReached, destination_n* list_destination_n, destination_n** p_list_destination_n_1, destination_n** p_tmp_destination_tail)
{

	RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

	mid_address tmp_addrs;
	memset( &tmp_addrs, 0, sizeof(mid_address));
	mid_address* tmp_addrsp;

	tmp_addrs.alias = addrReached;

	

	tmp_addrs.next_alias = OlsrLookupMidAliases(node, addrReached);
	tmp_addrsp = &tmp_addrs;

	while (tmp_addrsp != NULL)
	{

		// topo_dest is not in the routing table

		//Peter Modified and added to support olsr multi-path
		bool bExist = false;
		RouteEntryType ret = NOT_ALLOWED;


		double dDistance = 0.0;
		double dRWON = 0.0;


		if (_OLSR_MULTIPATH)
		{
			if (_TEST_TIME_COMPLEXITY)
			{

				dRWON = list_destination_n->destination->rt_entry_infos.related_neighbor->neighbor_infos.dDegreeWRTNode;
				dDistance = list_destination_n->destination->rt_entry_infos.related_neighbor->neighbor_infos.dDistanceWRTNode;
			}
			else
			{

				dRWON = ComputeRouterDegreeWRTOriginNode(node, list_destination_n->destination->rt_entry_infos.rtu_router.interfaceAddr.ipv4, &dDistance);
				dRWON = SimulateLocalDirectionOfAoA(node, dRWON);
			}
		}


		rt_entry* preExisting = NULL;


		rt_entry* rt_tmp = NULL;

		BOOL bSpecialCase = FALSE;

		
		{
			if (NULL != OlsrLookupRoutingTable(node, tmp_addrsp->alias, TRUE))
			{

				bExist = true;
			}
		}


		if (!bExist)
		{

			// PRINT OUT: Last Hop to Final Destination. The
			// function convert_address_to_string has to be
			// separately

			if (DEBUG)
			{
				char addrString[MAX_STRING_LENGTH];
				IO_ConvertIpAddressToString(
					&list_destination_n->destination->rt_dst,
					addrString);

				printf("%s -> ", addrString);

				IO_ConvertIpAddressToString(
					&addrReached,
					addrString);

				printf("%s\n", addrString);
			}

			destination_n* destination_n_1 = NULL;

			rt_entry* tmp = NULL;

			
			{
				if (rt_tmp != NULL)
				{
					tmp = rt_tmp;

					tmp->rt_entry_infos.rtu_router = list_destination_n->destination->rt_entry_infos.rtu_router;
					tmp->rt_entry_infos.rtu_interface = list_destination_n->destination->rt_interface;

					tmp->rt_entry_infos.rtu_lasthop = list_destination_n->destination->rt_entry_infos.rtu_dst;
					tmp->rt_entry_infos.rtu_metric = list_destination_n->destination->rt_entry_infos.rtu_metric + 1;

					
				}
				else
				{
					// changed by SRD for multiple iface problem
					tmp = OlsrInsertRoutingTablefromTopology(
						node,
						list_destination_n->destination,
						tmp_addrsp->alias,
						list_destination_n->destination->rt_dst,
						dRWON, dDistance, TRUE				
						);
				}				
				
			}

			

			// insert in routing table using topology
			if (tmp != NULL)
			{

				destination_n_1 = (destination_n *)
					MEM_malloc(sizeof(destination_n));

				memset(destination_n_1, 0, sizeof(destination_n));

				destination_n_1->destination = tmp;
			}
		

			if (destination_n_1 != NULL)
			{
				//Peter comment: add the new added entry to list_destination_n_1
				//destination_n_1->next = *p_list_destination_n_1;
				//*p_list_destination_n_1 = destination_n_1;



				if (*p_list_destination_n_1 == NULL)
				{
					*p_list_destination_n_1 = destination_n_1;
					*p_tmp_destination_tail = destination_n_1;
				}
				else
				{
					
					(*p_tmp_destination_tail)->next = destination_n_1;
					*p_tmp_destination_tail = (*p_tmp_destination_tail)->next;

					
				}
			}
		}
		tmp_addrsp = tmp_addrsp->next_alias;
	}
}




static void OlsrCalculateRoutingTableForSinglePathTopologySearchHelpFunc(Node * node, Address addrReached, destination_n* list_destination_n, destination_n** p_list_destination_n_1, destination_n** p_tmp_destination_tail, BOOL bAdvanced = FALSE, BOOL bReplace = FALSE, BOOL bOnlyCommonLasthop = FALSE, 
																		 UInt32 * puiLookupCnt = NULL, BOOL bRequireSameRouter = FALSE, BOOL * pbRediscovery = NULL)
{

	RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

	mid_address tmp_addrs;
	memset( &tmp_addrs, 0, sizeof(mid_address));
	mid_address* tmp_addrsp;

	tmp_addrs.alias = addrReached;

	//destination_n* tmp_destination_tail = NULL;


	tmp_addrs.next_alias = OlsrLookupMidAliases(node, addrReached);
	tmp_addrsp = &tmp_addrs;

	while (tmp_addrsp != NULL)
	{

		// topo_dest is not in the routing table

		//Peter Modified and added to support olsr multi-path
		bool bExist = false;
		RouteEntryType ret = NOT_ALLOWED;


		double dDistance = 0.0;
		double dRWON = 0.0;


		if (_OLSR_MULTIPATH)
		{
			if (_TEST_TIME_COMPLEXITY)
			{

				dRWON = list_destination_n->destination->rt_entry_infos.related_neighbor->neighbor_infos.dDegreeWRTNode;
				dDistance = list_destination_n->destination->rt_entry_infos.related_neighbor->neighbor_infos.dDistanceWRTNode;
			}
			else
			{

				dRWON = ComputeRouterDegreeWRTOriginNode(node, list_destination_n->destination->rt_entry_infos.rtu_router.interfaceAddr.ipv4, &dDistance);
				dRWON = SimulateLocalDirectionOfAoA(node, dRWON);
			}
		}


		rt_entry* preExisting = NULL;


		rt_entry* rt_tmp = NULL;

		BOOL bSpecialCase = FALSE;

		//bAdvanced: for optimized accumulative route re-calculation
		if (bAdvanced)
		{
			if (g_iAccumulativeRouteCalculation == 1 || g_iAccumulativeRouteCalculation == 2)
			{

				/*
				if (NULL != OlsrLookupRoutingTable(node, tmp_addrsp->alias))
				{

					bExist = true;
				}
				*/
			//}
			//else	//g_iAccumulativeRouteCalculation == 2
			//{

				if (bReplace)
				{


					if (list_destination_n->destination->rt_entry_infos.bDescendentRequireFurtherUpdate)
					{

							//printf("call OlsrLookupRoutingTableAdvForLastReplace \n");
						//???
						rt_entry* preConcludeFirst = NULL;
						preExisting = OlsrLookupRoutingTableAdvForLastReplace(node, tmp_addrsp->alias, list_destination_n->destination->rt_dst, 
							list_destination_n->destination->rt_router, list_destination_n->destination->rt_metric + 1, bOnlyCommonLasthop, bRequireSameRouter, &preConcludeFirst);

                                                //may need to check whether it already had been added to work set
						//??Or just try to check whether already satisfy the following conditions
						if (NULL != preExisting)
						{
							//already must have been commonlast
							if (preExisting->rt_entry_infos.rtu_router.interfaceAddr.ipv4 == list_destination_n->destination->rt_entry_infos.rtu_router.interfaceAddr.ipv4
								&& preExisting->rt_metric == list_destination_n->destination->rt_metric + 1)
							{
								preExisting = NULL;
							}							
						}
						

						if (NULL != preExisting)
						{

							preExisting->rt_entry_infos.uiCostChg = 0;
							preExisting->rt_entry_infos.bCostChanged = FALSE;
							preExisting->rt_entry_infos.bDescendentRequireFurtherUpdate = FALSE;
							preExisting->rt_entry_infos.bRequireDelete = FALSE;
							//preExisting->rt_entry_infos.bRequireExchange = FALSE;
							
							if (!list_destination_n->destination->rt_entry_infos.bRequireDelete)
							{

								if (list_destination_n->destination->rt_entry_infos.bCostChanged)
								{
									//preExisting->rt_entry_infos.bRequireExchange = TRUE;
								
								
									//DebugBreak();
									BOOL bExchangeFound = FindRouteExchange(node, preExisting, TRUE, puiLookupCnt, bRequireSameRouter);

									if (!bExchangeFound)
									{

										//this branch should never happen, since the success of find earlier level exchange
										//can ensure there is at least one suitable (maybe not perfect) option
										
										
										//OlsrDeleteRoutingTable(preExisting);
										//preExisting = NULL;

										//*pbRequireRediscovery = TRUE;
										//return NULL;
									}

								}
								else
								{
									//only route changed

									
									//preExisting->rt_entry_infos.bRequireExchange = FALSE;

									//preExisting->rt_entry_infos.bRequireUpdate = TRUE;

									preExisting->rt_interface = list_destination_n->destination->rt_interface;
									preExisting->rt_router = list_destination_n->destination->rt_router;

									if (_OLSR_MULTIPATH)
									{


										preExisting->rt_entry_infos.rtu_DegreeWRTNode = list_destination_n->destination->rt_entry_infos.rtu_DegreeWRTNode;
										preExisting->rt_entry_infos.rtu_DistanceWRTNode = list_destination_n->destination->rt_entry_infos.rtu_DistanceWRTNode;
										preExisting->rt_entry_infos.related_neighbor = list_destination_n->destination->rt_entry_infos.related_neighbor;
									}

									preExisting->rt_entry_infos.bDescendentRequireFurtherUpdate = TRUE;
									preExisting->rt_entry_infos.bCostChanged = FALSE;
									preExisting->rt_entry_infos.bRequireDelete = FALSE;

									preExisting->rt_entry_infos.uiCostChg = 0;
									


								}		

							}
							else
							{
								//delete

								if (preConcludeFirst != NULL)
								{
									//if there is more than one entry for this dest, then it can be delete
									if (preConcludeFirst->rt_entry_infos.oa_total_routes_count >= 2)
									{


										//OlsrDeleteRoutingTable(prte);


										preConcludeFirst->rt_entry_infos.oa_total_routes_count--;

										if (preExisting != preConcludeFirst)
										{
											OlsrRemoveList((olsr_qelem *)preExisting);
											//rt_entry* prteTmp = QueryRoutingTableAccordingToNodeId(node, tco_delete_list_tmp->nid);
										}
										else	//prte == prteFirst
										{

											OlsrRemoveList((olsr_qelem *)preExisting);

											rt_entry* prteTmpNewFirst = QueryRoutingTableAccordingToNodeId(node, preExisting->rt_entry_infos.rtu_dst.interfaceAddr.ipv4);

											if (prteTmpNewFirst != NULL)
											{


												if (_OLSR_MULTIPATH)
												{

													prteTmpNewFirst->rt_entry_infos.oa_total_routes_count = preExisting->rt_entry_infos.oa_total_routes_count;
													prteTmpNewFirst->rt_entry_infos.oa_dWeightedDirectionDiffer = preExisting->rt_entry_infos.oa_dWeightedDirectionDiffer;
													prteTmpNewFirst->rt_entry_infos.oa_maximum_allowed_cost = preExisting->rt_entry_infos.oa_maximum_allowed_cost;
												}

											}

										}



										preExisting->rt_entry_infos.bDescendentRequireFurtherUpdate = TRUE;

										preExisting->rt_entry_infos.bRequireDelete = TRUE;

										/*
										destination_n* list_destination_tmp;
										list_destination_tmp = (destination_n* )
											MEM_malloc(sizeof(destination_n));

										memset(
											list_destination_tmp,
											0,
											sizeof(destination_n));

										list_destination_tmp->destination = prte;
										list_destination_tmp->next = list_destination_n;
										list_destination_n = list_destination_tmp;
										*/


									}
									else	// < 2
									{

										if (pbRediscovery != NULL)
										{
											*pbRediscovery = TRUE;
										}
										//OlsrDeleteRoutingTable(prte);

										//bExist = false;
										break;

										//return;
									}

								}
								else
								{
									//should never happen
								}
							}
							
							bExist = true;
						}
						else
						{
							bExist = false;
						}

					}
					else
					{
						bExist = false;
					}

					


				}
				else
				{

					//printf("----------------------- call OlsrLookupRoutingTableAdv Begin \n");
					

					//Peter Comment: check whether it will indeed be reach if the last hop is a neighbor node with cost 1,
					//since if there is no such 2 hop neighbor with main_neighbor_addr equal this neighbor node,
					//then we can not consider this connection exist, even if according to last table it is!!!
					
					BOOL b2HopNeighborMismatchCausedDisconnect = FALSE;
					if (list_destination_n->destination->rt_metric == 1)
					{
						
						b2HopNeighborMismatchCausedDisconnect = TRUE;
						b2HopNeighborMismatchCausedDisconnect = DisconnectivetyCausedBy2HopNeighbor(node, tmp_addrsp->alias, list_destination_n->destination->rt_entry_infos.rtu_dst.interfaceAddr.ipv4);
						
					}


					if (b2HopNeighborMismatchCausedDisconnect)
					{

						bExist = true;
					}
					else
					{
						 //|| NULL != OlsrLookupRoutingTableAdv(node, tmp_addrsp->alias, list_destination_n->destination->rt_metric + 1)
						//OlsrLookupRoutingTableAdv(node, tmp_addrsp->alias, list_destination_n->destination->rt_metric + 1)

						rt_tmp = OlsrLookupRoutingTable(node, tmp_addrsp->alias);

						if (rt_tmp != NULL)
						{
							if (list_destination_n->destination->rt_metric + 1 < rt_tmp->rt_metric)
							{
								//TO_IMPROVE_PERFORMANCE
								/*
								if (olsr->bNeighborChgCausedRemoveFromHigherHop)
								{
									if (rt_tmp->rt_metric == MAX_COST)
									{
										remove_from_tco_node_addr_set(&olsr->recent_delete_list, rt_tmp->rt_entry_infos.rtu_dst.interfaceAddr.ipv4);										
									
									
										if (g_iToAchieveSameRoute == 1)
										{
											bSpecialCase = TRUE;
											//FindRouteExchangeV20(node, rt_tmp, TRUE);
										}										
									
									}

								}
								*/
								
								
																

								bExist = false;
							}
							else
							{
								if (g_iToAchieveSameRoute == 1)
								{
									if (list_destination_n->destination->rt_metric + 1 == rt_tmp->rt_metric 
										&& PreferredRouteForNew(list_destination_n->destination->rt_entry_infos.rtu_router.interfaceAddr.ipv4, rt_tmp->rt_entry_infos.rtu_router.interfaceAddr.ipv4))
									{
										bExist = false;
									}
									else
									{
										bExist = true;
									}
								}
								else
								{
									bExist = true;
								}
								
							}
						}
						else
						{
							bExist = false;
						}

					}

					//printf("----------------------- call OlsrLookupRoutingTableAdv End \n");
				}
				
			}
		}
		else
		{
			if (NULL != OlsrLookupRoutingTable(node, tmp_addrsp->alias))
			{

				bExist = true;
			}
		}


		if (!bReplace && !bExist || bExist && bReplace && preExisting != NULL)
		{

			// PRINT OUT: Last Hop to Final Destination. The
			// function convert_address_to_string has to be
			// separately

			if (DEBUG)
			{
				char addrString[MAX_STRING_LENGTH];
				IO_ConvertIpAddressToString(
					&list_destination_n->destination->rt_dst,
					addrString);

				printf("%s -> ", addrString);

				IO_ConvertIpAddressToString(
					&addrReached,
					addrString);

				printf("%s\n", addrString);
			}

			destination_n* destination_n_1 = NULL;

			rt_entry* tmp = NULL;

			if (bReplace)
			{
				if (preExisting->rt_entry_infos.bDescendentRequireFurtherUpdate)
				{
					
					tmp = preExisting;
				}				
				
			}
			else
			{
				if (rt_tmp != NULL)
				{
					tmp = rt_tmp;

					tmp->rt_entry_infos.rtu_router = list_destination_n->destination->rt_entry_infos.rtu_router;
					tmp->rt_entry_infos.rtu_interface = list_destination_n->destination->rt_interface;

					tmp->rt_entry_infos.rtu_lasthop = list_destination_n->destination->rt_entry_infos.rtu_dst;
					tmp->rt_entry_infos.rtu_metric = list_destination_n->destination->rt_entry_infos.rtu_metric + 1;

					/*
					if (g_iToAchieveSameRoute == 1 && bSpecialCase)
					{
						//bSpecialCase = TRUE;
						FindRouteExchangeV20(node, rt_tmp, TRUE);
					}
					*/

				}
				else
				{
					// changed by SRD for multiple iface problem
					tmp = OlsrInsertRoutingTablefromTopology(
						node,
						list_destination_n->destination,
						tmp_addrsp->alias,
						list_destination_n->destination->rt_dst,
						dRWON, dDistance				
						);
				}				
				
			}

			

			// insert in routing table using topology
			if (tmp != NULL)
			{
				destination_n_1 = (destination_n *)
					MEM_malloc(sizeof(destination_n));

				memset(destination_n_1, 0, sizeof(destination_n));

				destination_n_1->destination = tmp;
			}
			
			if (destination_n_1 != NULL)
			{
				//Peter comment: add the new added entry to list_destination_n_1
				//destination_n_1->next = *p_list_destination_n_1;
				//*p_list_destination_n_1 = destination_n_1;



				if (*p_list_destination_n_1 == NULL)
				{
					*p_list_destination_n_1 = destination_n_1;
					*p_tmp_destination_tail = destination_n_1;
				}
				else
				{
					
					(*p_tmp_destination_tail)->next = destination_n_1;
					*p_tmp_destination_tail = (*p_tmp_destination_tail)->next;

					//(*p_list_destination_n_1)->next = destination_n_1;
				}
			}
		}
		tmp_addrsp = tmp_addrsp->next_alias;
	}
}



static void OlsrCalculateRoutingTableForSinglePathTopologySearchHelpFuncV24(Node * node, destination_n * dCorrespondingChild, Address addrReached, destination_n* list_destination_n, destination_n** p_current_p0, destination_n** p_list_tmp, UInt32 * puiLookupCnt = NULL, tco_node_addr ** ptna = NULL, tco_node_addr ** ptna_avoid = NULL, tco_node_addr ** ptna_avoid2 = NULL)
{

	mid_address tmp_addrs;
	memset( &tmp_addrs, 0, sizeof(mid_address));
	mid_address* tmp_addrsp;

	tmp_addrs.alias = addrReached;


	tmp_addrs.next_alias = OlsrLookupMidAliases(node, addrReached);
	tmp_addrsp = &tmp_addrs;

	while (tmp_addrsp != NULL)
	{

		// topo_dest is not in the routing table

		//Peter Modified and added to support olsr multi-path
		bool bExist = false;
		RouteEntryType ret = NOT_ALLOWED;


		double dDistance = 0.0;
		double dRWON = 0.0;


		if (_OLSR_MULTIPATH)
		{
			if (_TEST_TIME_COMPLEXITY)
			{

				dRWON = list_destination_n->destination->rt_entry_infos.related_neighbor->neighbor_infos.dDegreeWRTNode;
				dDistance = list_destination_n->destination->rt_entry_infos.related_neighbor->neighbor_infos.dDistanceWRTNode;
			}
			else
			{

				dRWON = ComputeRouterDegreeWRTOriginNode(node, list_destination_n->destination->rt_entry_infos.rtu_router.interfaceAddr.ipv4, &dDistance);
				dRWON = SimulateLocalDirectionOfAoA(node, dRWON);
			}

		}

		

		rt_entry* preExisting = NULL;

		//bAdvanced: for optimized accumulative route re-calculation
		
		
			//g_iAccumulativeRouteCalculation == 2
		{

			
			if (list_destination_n->destination->rt_entry_infos.bDescendentRequireFurtherUpdate)
			{

					//printf("call OlsrLookupRoutingTableAdvForLastReplace \n");
				//???
				//rt_entry* preConcludeFirst = NULL;

				if (dCorrespondingChild != NULL)
				{
					
					preExisting = dCorrespondingChild->destination;
				}
				else
				{

					preExisting = OlsrLookupRoutingTableAdvForLastReplace(node, tmp_addrsp->alias, list_destination_n->destination->rt_dst, 
						list_destination_n->destination->rt_router, list_destination_n->destination->rt_metric + 1, TRUE);
				}


				//may need to check whether it already had been added to work set
				//??Or just try to check whether already satisfy the following conditions
				if (NULL != preExisting)
				{
					//already must have been commonlast
					if (preExisting->rt_entry_infos.rtu_router.interfaceAddr.ipv4 == list_destination_n->destination->rt_entry_infos.rtu_router.interfaceAddr.ipv4
						&& preExisting->rt_metric == list_destination_n->destination->rt_metric + 1)
					{
						//consider this as the entry already be added into the n_1 table,
						//since the exchange function may cause lasthop change, so update again will cause the disappear of further update and cause problem.
						//and the exchange means it has already be added to lists, so add again will cause problem as well
						
						preExisting = NULL;
					}							
				}
				


				if (NULL != preExisting)
				{

					preExisting->rt_entry_infos.bCostChanged = FALSE;
					preExisting->rt_entry_infos.bDescendentRequireFurtherUpdate = FALSE;
					preExisting->rt_entry_infos.bRequireDelete = FALSE;

					preExisting->rt_entry_infos.uiCostChg = 0;
					

					if (list_destination_n->destination->rt_entry_infos.uiCostChg == 1)
					{

						BOOL bExchangeFound = FindRouteExchangeV20(node, dCorrespondingChild, preExisting, FALSE, puiLookupCnt, FALSE, ptna_avoid, ptna_avoid2);

						if (bExchangeFound)
						{
							if (preExisting->rt_entry_infos.bDescendentRequireFurtherUpdate)
							{
								//only route change in this case
								//add to n_1???
								//add to n_1


							}
							else
							{
								//perfect change							
								preExisting = NULL;

								
							
							}

						}
						else
						{
							//add to 

							if (ptna != NULL)
							{
								insert_into_tco_node_addr_set(ptna, addrReached.interfaceAddr.ipv4);

								//add to avoid consider list

								destination_n* destination_n_1 = (destination_n *)
									MEM_malloc(sizeof(destination_n));

								memset(destination_n_1, 0, sizeof(destination_n));

								//special case, save the (+2) last hop's route related infos, except the cost+1

								//preExisting->rt_entry_infos.rtu_lasthop = prtetmp->rt_dst;
								
								/*
								rt_entry*  prtetmp = list_destination_n->destination;


								preExisting->rt_interface = prtetmp->rt_interface;
								preExisting->rt_router = prtetmp->rt_router;


								preExisting->rt_entry_infos.rtu_DegreeWRTNode = prtetmp->rt_entry_infos.rtu_DegreeWRTNode;
								preExisting->rt_entry_infos.rtu_DistanceWRTNode = prtetmp->rt_entry_infos.rtu_DistanceWRTNode;
								preExisting->rt_entry_infos.related_neighbor = prtetmp->rt_entry_infos.related_neighbor;

								*/

								destination_n_1->destination = preExisting;

								if (dCorrespondingChild != NULL)
								{
									destination_n_1->children = dCorrespondingChild->children;
									destination_n_1->bChildrenDetermined = dCorrespondingChild->bChildrenDetermined;

									dCorrespondingChild->children = NULL;
								}


								destination_n_1->next = *p_list_tmp;
								*p_list_tmp = destination_n_1;
							}
						}
					
					}
					else
					{
						//should not happen

					}		

					
				
					
					bExist = true;
				}
				else
				{
					bExist = false;
				}

			}
			else
			{
				bExist = false;
			}
			
		}
				

		if (bExist && preExisting != NULL)
		{

			// PRINT OUT: Last Hop to Final Destination. The
			// function convert_address_to_string has to be
			// separately

			if (DEBUG)
			{
				char addrString[MAX_STRING_LENGTH];
				IO_ConvertIpAddressToString(
					&list_destination_n->destination->rt_dst,
					addrString);

				printf("%s -> ", addrString);

				IO_ConvertIpAddressToString(
					&addrReached,
					addrString);

				printf("%s\n", addrString);
			}

			destination_n* destination_n_1 = NULL;

			rt_entry* tmp = NULL;

			
			if (preExisting->rt_entry_infos.bDescendentRequireFurtherUpdate)
			{
				
				tmp = preExisting;
			}				
				
			
			// insert in routing table using topology
			if (tmp != NULL)
			{

				destination_n_1 = (destination_n *)
					MEM_malloc(sizeof(destination_n));

				memset(destination_n_1, 0, sizeof(destination_n));

				destination_n_1->destination = tmp;

				if (dCorrespondingChild != NULL)
				{
					destination_n_1->children = dCorrespondingChild->children;
					destination_n_1->bChildrenDetermined = dCorrespondingChild->bChildrenDetermined;

					dCorrespondingChild->children = NULL;
				}
			}
		

			if (destination_n_1 != NULL)
			{
				
				//!!! in this function, cost change mean only cost plus one change 
				
				//Peter comment: add the new added entry to p_list_destination_n_0 or p_list_destination_n_1
				//BOOL bLastHopCostChg = list_destination_n->destination->rt_entry_infos.bCostChanged;

				UInt16 uiLastHopCostChg = list_destination_n->destination->rt_entry_infos.uiCostChg;

				if (uiLastHopCostChg == 1)
				{
					
					
					//DebugBreak();
					//if (preExisting->rt_entry_infos.bDescendentRequireFurtherUpdate)
					{

						//find 0 exchange
						destination_n_1->next = *p_current_p0;
						*p_current_p0 = destination_n_1;

					}
					//else
					{

						
					}
						
				
				}
				

				
				/*
				if (preExisting->rt_entry_infos.bCostChanged)
				{
					
					destination_n_1->next = *p_list_destination_n_2;
					*p_list_destination_n_2 = destination_n_1;

				}
				else
				{
					destination_n_1->next = *p_list_destination_n_1;
					*p_list_destination_n_1 = destination_n_1;
				}
				*/
				
			}
		}
		tmp_addrsp = tmp_addrsp->next_alias;
	}
}



static void OlsrCalculateRoutingTableForSinglePathTopologySearchHelpFuncV23(Node * node, destination_n * dCorrespondingChild, e2_s e2_current, Address addrReached, destination_n* list_destination_n, destination_n** p_minus_1_p0, destination_n** p_list_tmp, UInt32 * puiLookupCnt = NULL, tco_node_addr ** ptna = NULL)
{

	mid_address tmp_addrs;
	memset( &tmp_addrs, 0, sizeof(mid_address));
	mid_address* tmp_addrsp;

	tmp_addrs.alias = addrReached;


	tmp_addrs.next_alias = OlsrLookupMidAliases(node, addrReached);
	tmp_addrsp = &tmp_addrs;

	while (tmp_addrsp != NULL)
	{

		// topo_dest is not in the routing table

		//Peter Modified and added to support olsr multi-path
		bool bExist = false;
		RouteEntryType ret = NOT_ALLOWED;


		double dDistance = 0.0;
		double dRWON = 0.0;


		if (_OLSR_MULTIPATH)
		{	

			if (_TEST_TIME_COMPLEXITY)
			{

				dRWON = list_destination_n->destination->rt_entry_infos.related_neighbor->neighbor_infos.dDegreeWRTNode;
				dDistance = list_destination_n->destination->rt_entry_infos.related_neighbor->neighbor_infos.dDistanceWRTNode;
			}
			else
			{

				dRWON = ComputeRouterDegreeWRTOriginNode(node, list_destination_n->destination->rt_entry_infos.rtu_router.interfaceAddr.ipv4, &dDistance);
				dRWON = SimulateLocalDirectionOfAoA(node, dRWON);
			}
		}

		


		rt_entry* preExisting = NULL;

		//bAdvanced: for optimized accumulative route re-calculation
		
		if (g_iAccumulativeRouteCalculation == 1)
		{

			if (NULL != OlsrLookupRoutingTable(node, tmp_addrsp->alias))
			{

				bExist = true;
			}
		}
		else	//g_iAccumulativeRouteCalculation == 2
		{

			
			if (list_destination_n->destination->rt_entry_infos.bDescendentRequireFurtherUpdate)
			{

					//printf("call OlsrLookupRoutingTableAdvForLastReplace \n");
				//???
				//rt_entry* preConcludeFirst = NULL;


				if (dCorrespondingChild != NULL)
				{

					preExisting = dCorrespondingChild->destination;
				}
				else
				{

					preExisting = OlsrLookupRoutingTableAdvForLastReplace(node, tmp_addrsp->alias, list_destination_n->destination->rt_dst, 
						list_destination_n->destination->rt_router, list_destination_n->destination->rt_metric + 1, TRUE);
				}


				
				//may need to check whether it already had been added to work set
				//??Or just try to check whether already satisfy the following conditions
				if (NULL != preExisting)
				{
					//already must have been common-last
					if (preExisting->rt_entry_infos.rtu_router.interfaceAddr.ipv4 == list_destination_n->destination->rt_entry_infos.rtu_router.interfaceAddr.ipv4
						&& preExisting->rt_metric == list_destination_n->destination->rt_metric + 1)
					{
						//consider this as the entry already be added into the n_1 table,
						//since the exchange function may cause lasthop change, so update again will cause the disappear of further update and cause problem.
						//and the exchange means it has already be added to lists, so add again will cause problem as well
						
						preExisting = NULL;
					}							
				}
				


				if (NULL != preExisting)
				{

					preExisting->rt_entry_infos.bCostChanged = FALSE;
					preExisting->rt_entry_infos.bDescendentRequireFurtherUpdate = FALSE;
					preExisting->rt_entry_infos.bRequireDelete = FALSE;

					preExisting->rt_entry_infos.uiCostChg = 0;
					

					if (list_destination_n->destination->rt_entry_infos.uiCostChg == 2)
					{

						BOOL bExchangeFound = FindRouteExchangeV20(node, dCorrespondingChild, preExisting, TRUE, puiLookupCnt);
						if (bExchangeFound)
						{
							if (g_iToAchieveSameRoute == 1)
							{
								//Peter Comment: a very special case for same route support,
								//since the +0 exchange for children of entry X in +2 list,
								//may potentially become parent of X, which may cause route change. 
								//in addition, it will also become the parent of any entry Y in +1 list

								tco_node_addr * adjacents_backup = NULL;
								topology_last_entry * t_last_sym = OlsrLookupLastTopologyTableSYM(node, preExisting->rt_dst);
								
								if (t_last_sym != NULL)
								{

									destination_list* topo_dest = NULL;

									topo_dest = t_last_sym->topology_list_of_destinations;

									

									while (topo_dest != NULL)
									{

										Address addrReached = topo_dest->destination_node->topology_destination_dst;

										insert_into_tco_node_addr_set(&(adjacents_backup), addrReached.interfaceAddr.ipv4);

										topo_dest = topo_dest->next;
										
									}
								}


								destination_n* tmp_destination_1 = e2_current.list_p2;

								while (tmp_destination_1 != NULL)
								{

									//it has to be adjacent with the new +0 exchange 
									if (exist_in_tco_node_addr_set(&adjacents_backup, tmp_destination_1->destination->rt_entry_infos.rtu_dst.interfaceAddr.ipv4))
									{
										if (PreferredRouteForNew(preExisting->rt_entry_infos.rtu_router.interfaceAddr.ipv4, tmp_destination_1->destination->rt_entry_infos.rtu_router.interfaceAddr.ipv4))
										{
											//change route for its old parent to become the new parent

											tmp_destination_1->destination->rt_interface = preExisting->rt_interface;

							
								
											/*
											if (_OLSR_MULTIPATH)
											{

											
												tmp_destination_1->destination->rt_entry_infos.rtu_DegreeWRTNode = preExisting->rt_entry_infos.rtu_DegreeWRTNode;
												tmp_destination_1->destination->rt_entry_infos.rtu_DistanceWRTNode = preExisting->rt_entry_infos.rtu_DistanceWRTNode;
												tmp_destination_1->destination->rt_entry_infos.related_neighbor = preExisting->rt_entry_infos.related_neighbor;
											}
											*/
																
								
											tmp_destination_1->destination->rt_entry_infos.rtu_lasthop = preExisting->rt_entry_infos.rtu_dst;									
											
											tmp_destination_1->destination->rt_router = preExisting->rt_router;									
											
										}	
									}								


									tmp_destination_1 = tmp_destination_1->next;
								}


								tmp_destination_1 = e2_current.list_p1;

								while (tmp_destination_1 != NULL)
								{

									//it has to be adjacent with the new +0 exchange 
									if (exist_in_tco_node_addr_set(&adjacents_backup, tmp_destination_1->destination->rt_entry_infos.rtu_dst.interfaceAddr.ipv4))
									{

										if (PreferredRouteForNew(preExisting->rt_entry_infos.rtu_router.interfaceAddr.ipv4, tmp_destination_1->destination->rt_entry_infos.rtu_router.interfaceAddr.ipv4))
										{
											//change route for its old parent to become the new parent

											tmp_destination_1->destination->rt_interface = preExisting->rt_interface;

							
								
											/*
											if (_OLSR_MULTIPATH)
											{

											
												tmp_destination_1->destination->rt_entry_infos.rtu_DegreeWRTNode = preExisting->rt_entry_infos.rtu_DegreeWRTNode;
												tmp_destination_1->destination->rt_entry_infos.rtu_DistanceWRTNode = preExisting->rt_entry_infos.rtu_DistanceWRTNode;
												tmp_destination_1->destination->rt_entry_infos.related_neighbor = preExisting->rt_entry_infos.related_neighbor;
											}
											*/
																
								
											tmp_destination_1->destination->rt_entry_infos.rtu_lasthop = preExisting->rt_entry_infos.rtu_dst;									
											
											tmp_destination_1->destination->rt_router = preExisting->rt_router;									
											
										}	
									}								


									tmp_destination_1 = tmp_destination_1->next;
								}

								

								clear_tco_node_addr_set(&adjacents_backup);															
								
							}

							if (preExisting->rt_entry_infos.bDescendentRequireFurtherUpdate)
							{
								//only route change in this case
								//add to n_1???
								//add to n_1
							}
							else
							{
								//perfect change							
								preExisting = NULL;
							
							}

						}
						else
						{
							//add to 

							if (ptna != NULL)
							{
								insert_into_tco_node_addr_set(ptna, addrReached.interfaceAddr.ipv4);

								//add to avoid consider list

								destination_n* destination_n_1 = (destination_n *)
									MEM_malloc(sizeof(destination_n));

								memset(destination_n_1, 0, sizeof(destination_n));

								
								if (g_iToAchieveSameRoute != 1)
								{

									//special case, save the (+2) last hop's route related infos, except the cost+1
									//for convenient update of +2

									//preExisting->rt_entry_infos.rtu_lasthop = prtetmp->rt_dst;
									rt_entry*  prtetmp = list_destination_n->destination;


									preExisting->rt_interface = prtetmp->rt_interface;
									preExisting->rt_router = prtetmp->rt_router;


									if (_OLSR_MULTIPATH)
									{
										preExisting->rt_entry_infos.rtu_DegreeWRTNode = prtetmp->rt_entry_infos.rtu_DegreeWRTNode;
										preExisting->rt_entry_infos.rtu_DistanceWRTNode = prtetmp->rt_entry_infos.rtu_DistanceWRTNode;
										preExisting->rt_entry_infos.related_neighbor = prtetmp->rt_entry_infos.related_neighbor;
									}
								

								}

								if (dCorrespondingChild != NULL)
								{
									destination_n_1->children = dCorrespondingChild->children;
									destination_n_1->bChildrenDetermined = dCorrespondingChild->bChildrenDetermined;

									dCorrespondingChild->children = NULL;
								}

								
								destination_n_1->destination = preExisting;


								destination_n_1->next = *p_list_tmp;
								*p_list_tmp = destination_n_1;
							}
						}
					
					}
					else
					{
						//should not happen

					}		

					
				
					
					bExist = true;
				}
				else
				{
					bExist = false;
				}

			}
			else
			{
				bExist = false;
			}
			
		}
				

		if (bExist && preExisting != NULL)
		{

			// PRINT OUT: Last Hop to Final Destination. The
			// function convert_address_to_string has to be
			// separately

			if (DEBUG)
			{
				char addrString[MAX_STRING_LENGTH];
				IO_ConvertIpAddressToString(
					&list_destination_n->destination->rt_dst,
					addrString);

				printf("%s -> ", addrString);

				IO_ConvertIpAddressToString(
					&addrReached,
					addrString);

				printf("%s\n", addrString);
			}

			destination_n* destination_n_1 = NULL;

			rt_entry* tmp = NULL;

			
			if (preExisting->rt_entry_infos.bDescendentRequireFurtherUpdate)
			{
				
				tmp = preExisting;
			}				
				
			
			// insert in routing table using topology
			if (tmp != NULL)
			{
				destination_n_1 = (destination_n *)
					MEM_malloc(sizeof(destination_n));

				memset(destination_n_1, 0, sizeof(destination_n));

				destination_n_1->destination = tmp;

				if (dCorrespondingChild != NULL)
				{
					destination_n_1->children = dCorrespondingChild->children;
					destination_n_1->bChildrenDetermined = dCorrespondingChild->bChildrenDetermined;

					dCorrespondingChild->children = NULL;
				}
			}
		

			if (destination_n_1 != NULL)
			{
				
				//!!! in this function, cost change mean only cost plus one change 
				
				//Peter comment: add the new added entry to p_list_destination_n_0 or p_list_destination_n_1
				//BOOL bLastHopCostChg = list_destination_n->destination->rt_entry_infos.bCostChanged;

				UInt16 uiLastHopCostChg = list_destination_n->destination->rt_entry_infos.uiCostChg;

				if (uiLastHopCostChg == 2)
				{
					
					
					//DebugBreak();
					//if (preExisting->rt_entry_infos.bDescendentRequireFurtherUpdate)
					{

						//find 0 exchange
						destination_n_1->next = *p_minus_1_p0;
						*p_minus_1_p0 = destination_n_1;

					}
					//else
					{

						
					}
						
				
				}
				

				
				/*
				if (preExisting->rt_entry_infos.bCostChanged)
				{
					
					destination_n_1->next = *p_list_destination_n_2;
					*p_list_destination_n_2 = destination_n_1;

				}
				else
				{
					destination_n_1->next = *p_list_destination_n_1;
					*p_list_destination_n_1 = destination_n_1;
				}
				*/
				
			}
		}
		tmp_addrsp = tmp_addrsp->next_alias;
	}
}


static void OlsrCalculateRoutingTableForSinglePathTopologySearchHelpFuncV22(Node * node, destination_n * dCorrespondingChild, Address addrReached, destination_n* list_destination_n, e2_s* p_e2s_n_minus_1, e2_s* p_e2s_n_0, e2_s* p_e2s_n_1, UInt32 * puiLookupCnt = NULL, tco_node_addr ** ptna_set = NULL, tco_node_addr ** ptna_set2 = NULL)
{

	mid_address tmp_addrs;
	memset( &tmp_addrs, 0, sizeof(mid_address));
	mid_address* tmp_addrsp;

	tmp_addrs.alias = addrReached;


	tmp_addrs.next_alias = OlsrLookupMidAliases(node, addrReached);
	tmp_addrsp = &tmp_addrs;

	while (tmp_addrsp != NULL)
	{

		// topo_dest is not in the routing table

		//Peter Modified and added to support olsr multi-path
		bool bExist = false;
		RouteEntryType ret = NOT_ALLOWED;


		double dDistance = 0.0;
		double dRWON = 0.0;

		
		//if (bForPlus2)
		{

		}
		//else
		{

			if (_OLSR_MULTIPATH)
			{
				if (_TEST_TIME_COMPLEXITY)
				{

					dRWON = list_destination_n->destination->rt_entry_infos.related_neighbor->neighbor_infos.dDegreeWRTNode;
					dDistance = list_destination_n->destination->rt_entry_infos.related_neighbor->neighbor_infos.dDistanceWRTNode;
				}
				else
				{

					dRWON = ComputeRouterDegreeWRTOriginNode(node, list_destination_n->destination->rt_entry_infos.rtu_router.interfaceAddr.ipv4, &dDistance);
					dRWON = SimulateLocalDirectionOfAoA(node, dRWON);
				}
			}

			
		}
		

		rt_entry* preExisting = NULL;

		//bAdvanced: for optimized accumulative route re-calculation
		
		if (g_iAccumulativeRouteCalculation == 1)
		{

			if (NULL != OlsrLookupRoutingTable(node, tmp_addrsp->alias))
			{

				bExist = true;
			}
		}
		else	//g_iAccumulativeRouteCalculation == 2
		{

			/*
			if (bForPlus2)
			{
				preExisting = list_destination_n->destination;

				preExisting->rt_entry_infos.bCostChanged = FALSE;
				preExisting->rt_entry_infos.bDescendentRequireFurtherUpdate = FALSE;
				preExisting->rt_entry_infos.bRequireDelete = FALSE;

				preExisting->rt_entry_infos.uiCostChg = 0;
			}
			*/
			//else
			{
				if (list_destination_n->destination->rt_entry_infos.bDescendentRequireFurtherUpdate)
				{

						//printf("call OlsrLookupRoutingTableAdvForLastReplace \n");
					//???
					//rt_entry* preConcludeFirst = NULL;

					if (dCorrespondingChild != NULL)
					{
						preExisting = dCorrespondingChild->destination;
					}
					else
					{

						preExisting = OlsrLookupRoutingTableAdvForLastReplace(node, tmp_addrsp->alias, list_destination_n->destination->rt_dst, 
							list_destination_n->destination->rt_router, list_destination_n->destination->rt_metric + 1, TRUE);
					}

					
					//may need to check whether it already had been added to work set
					//??Or just try to check whether already satisfy the following conditions
					if (NULL != preExisting)
					{
						//already must have been commonlast
						if (preExisting->rt_entry_infos.rtu_router.interfaceAddr.ipv4 == list_destination_n->destination->rt_entry_infos.rtu_router.interfaceAddr.ipv4
							&& preExisting->rt_metric == list_destination_n->destination->rt_metric + 1)
						{
							//consider this as the entry already be added into the n_1 table,
							//since the exchange function may cause lasthop change, so update again will cause the disappear of further update and cause problem.
							//and the exchange means it has already be added to lists, so add again will cause problem as well
							
							preExisting = NULL;
						}							
					}
					


					if (NULL != preExisting)
					{

						preExisting->rt_entry_infos.bCostChanged = FALSE;
						preExisting->rt_entry_infos.bDescendentRequireFurtherUpdate = FALSE;
						preExisting->rt_entry_infos.bRequireDelete = FALSE;

						preExisting->rt_entry_infos.uiCostChg = 0;
						

						if (list_destination_n->destination->rt_entry_infos.uiCostChg != 0)
						{
							//preExisting->rt_entry_infos.bRequireExchange = TRUE;
						
						

							if (list_destination_n->destination->rt_entry_infos.uiCostChg == 1)
							{
								
								//DebugBreak();
								BOOL bExchangeFound = FindRouteExchangeV21(node, dCorrespondingChild, preExisting, TRUE, list_destination_n->destination, puiLookupCnt, FALSE, ptna_set, ptna_set2);

								if (!bExchangeFound)
								{

									//this branch should never happen, since the success of find earlier level exchange
									//can ensure there is at least one suitable (maybe not perfect) option
									
									
								}
								else
								{
									if (preExisting->rt_entry_infos.bDescendentRequireFurtherUpdate)
									{

										/*
										if (preExisting->rt_entry_infos.bCostChanged)
										{
											//add to n_2???
											//add to n_1
										}
										else
										{
											//route change 
											//add to n_1???
											//DebugBreak();
											//add to n_0
										
										}
										*/
										
										
									}
									else
									{
										preExisting = NULL;
									}
								}
							}
							else //2
							{


								BOOL bExchangeFound = FindRouteExchangeV22(node, dCorrespondingChild, preExisting, TRUE, list_destination_n->destination, puiLookupCnt, FALSE, ptna_set, ptna_set2);

								if (!bExchangeFound)
								{

									//this branch should never happen, since the success of find earlier level exchange
									//can ensure there is at least one suitable (maybe not perfect) option
									
									
								}
								else
								{
									if (preExisting->rt_entry_infos.bDescendentRequireFurtherUpdate)
									{

										/*
										if (preExisting->rt_entry_infos.bCostChanged)
										{
											//add to n_2???
											//add to n_1
										}
										else
										{
											//route change 
											//add to n_1???
											//DebugBreak();
											//add to n_0
										
										}
										*/
										
										
									}
									else
									{
										preExisting = NULL;
									}
								}

														
							
							}



						}
						else
						{
							//only route changed

							
							//preExisting->rt_entry_infos.bRequireExchange = FALSE;

							//preExisting->rt_entry_infos.bRequireUpdate = TRUE;

							BOOL bExchangeFound = FindRouteExchangeV20(node, dCorrespondingChild, preExisting, TRUE, puiLookupCnt, FALSE, ptna_set, ptna_set2);

							if (bExchangeFound)
							{
								if (preExisting->rt_entry_infos.bDescendentRequireFurtherUpdate)
								{
									//only route change in this case
									//add to n_1???
									//add to n_1
								}
								else
								{
									preExisting = NULL;
								}

							}
							else
							{
								//will never happen
							}

						}		

						
					
						
						bExist = true;
					}
					else
					{
						bExist = false;
					}

				}
				else
				{
					bExist = false;
				}
			}


			
			
		}
				

		if (bExist && preExisting != NULL)
		{

			// PRINT OUT: Last Hop to Final Destination. The
			// function convert_address_to_string has to be
			// separately

			if (DEBUG)
			{
				char addrString[MAX_STRING_LENGTH];
				IO_ConvertIpAddressToString(
					&list_destination_n->destination->rt_dst,
					addrString);

				printf("%s -> ", addrString);

				IO_ConvertIpAddressToString(
					&addrReached,
					addrString);

				printf("%s\n", addrString);
			}

			destination_n* destination_n_1 = NULL;

			rt_entry* tmp = NULL;

			
			if (preExisting->rt_entry_infos.bDescendentRequireFurtherUpdate)
			{
				
				tmp = preExisting;
			}				
				
			
			// insert in routing table using topology
			if (tmp != NULL)
			{

				destination_n_1 = (destination_n *)
					MEM_malloc(sizeof(destination_n));

				memset(destination_n_1, 0, sizeof(destination_n));


				destination_n_1->destination = tmp;

				if (dCorrespondingChild != NULL)
				{
					destination_n_1->children = dCorrespondingChild->children;
					destination_n_1->bChildrenDetermined = dCorrespondingChild->bChildrenDetermined;

					dCorrespondingChild->children = NULL;
				}
			}
		

			if (destination_n_1 != NULL)
			{
				
				//!!! in this function, cost change mean only cost plus one change 
				
				//Peter comment: add the new added entry to p_list_destination_n_0 or p_list_destination_n_1
				//BOOL bLastHopCostChg = list_destination_n->destination->rt_entry_infos.bCostChanged;

				UInt16 uiLastHopCostChg = list_destination_n->destination->rt_entry_infos.uiCostChg;

				if (uiLastHopCostChg != 0)
				{
					if (uiLastHopCostChg == 1)
					{
						//add to p_list_destination_n_1

						if (preExisting->rt_entry_infos.uiCostChg == 0)
						{
							destination_n_1->next = p_e2s_n_0->list_p0;
							p_e2s_n_0->list_p0 = destination_n_1;

						}
						else	//1
						{
							//destination_n_1->next = *p_list_destination_n_1;
							//*p_list_destination_n_1 = destination_n_1;

							destination_n_1->next = p_e2s_n_1->list_p1;
							p_e2s_n_1->list_p1 = destination_n_1;
						}

						
					}
					else	//uiLastHopCostChg == 2
					{
						//DebugBreak();
						if (preExisting->rt_entry_infos.uiCostChg == 0)
						{

							//skip
						}
						else
						{

							if (preExisting->rt_entry_infos.uiCostChg == 1)
							{
								destination_n_1->next = p_e2s_n_0->list_p1;
								p_e2s_n_0->list_p1 = destination_n_1;

							}
							else //2
							{
								destination_n_1->next = p_e2s_n_1->list_p2;
								p_e2s_n_1->list_p2 = destination_n_1;
							}
						}
						
						//add to p_list_destination_n_0, the current list, so it is tricky
						//destination_n* destination_n_tmp = NULL;
						//destination_n_tmp = (*p_list_destination_n_0)->next;
						//destination_n_1->next = destination_n_tmp;
						//(*p_list_destination_n_0)->next = destination_n_1;
						
						//*p_list_destination_n_0 = destination_n_1;

					}
				}
				else
				{
					
					{
						//add to p_list_destination_n_1
						destination_n_1->next = p_e2s_n_1->list_p0;
						p_e2s_n_1->list_p0 = destination_n_1;
					}
				}

				
				/*
				if (preExisting->rt_entry_infos.bCostChanged)
				{
					
					destination_n_1->next = *p_list_destination_n_2;
					*p_list_destination_n_2 = destination_n_1;

				}
				else
				{
					destination_n_1->next = *p_list_destination_n_1;
					*p_list_destination_n_1 = destination_n_1;
				}
				*/
				
			}
		}
		tmp_addrsp = tmp_addrsp->next_alias;
	}
}


static void OlsrCalculateRoutingTableForSinglePathTopologySearchHelpFuncV21(Node * node, Address addrReached, destination_n* list_destination_n, destination_n** p_list_destination_n_0, destination_n** p_list_destination_n_1, UInt32 * puiLookupCnt = NULL)
{

	mid_address tmp_addrs;
	memset( &tmp_addrs, 0, sizeof(mid_address));
	mid_address* tmp_addrsp;

	tmp_addrs.alias = addrReached;


	tmp_addrs.next_alias = OlsrLookupMidAliases(node, addrReached);
	tmp_addrsp = &tmp_addrs;

	while (tmp_addrsp != NULL)
	{

		// topo_dest is not in the routing table

		//Peter Modified and added to support olsr multi-path
		bool bExist = false;
		RouteEntryType ret = NOT_ALLOWED;


		double dDistance = 0.0;
		double dRWON = 0.0;

		if (_OLSR_MULTIPATH)
		{
			if (_TEST_TIME_COMPLEXITY)
			{

				dRWON = list_destination_n->destination->rt_entry_infos.related_neighbor->neighbor_infos.dDegreeWRTNode;
				dDistance = list_destination_n->destination->rt_entry_infos.related_neighbor->neighbor_infos.dDistanceWRTNode;
			}
			else
			{

				dRWON = ComputeRouterDegreeWRTOriginNode(node, list_destination_n->destination->rt_entry_infos.rtu_router.interfaceAddr.ipv4, &dDistance);
				dRWON = SimulateLocalDirectionOfAoA(node, dRWON);
			}
		}	
		


		rt_entry* preExisting = NULL;

		//bAdvanced: for optimized accumulative route re-calculation
		
		if (g_iAccumulativeRouteCalculation == 1)
		{

			if (NULL != OlsrLookupRoutingTable(node, tmp_addrsp->alias))
			{

				bExist = true;
			}
		}
		else	//g_iAccumulativeRouteCalculation == 2
		{

			
			if (list_destination_n->destination->rt_entry_infos.bDescendentRequireFurtherUpdate)
			{

					//printf("call OlsrLookupRoutingTableAdvForLastReplace \n");
				//???
				//rt_entry* preConcludeFirst = NULL;
				preExisting = OlsrLookupRoutingTableAdvForLastReplace(node, tmp_addrsp->alias, list_destination_n->destination->rt_dst, 
					list_destination_n->destination->rt_router, list_destination_n->destination->rt_metric + 1, TRUE);


				
				//may need to check whether it already had been added to work set
				//??Or just try to check whether already satisfy the following conditions
				if (NULL != preExisting)
				{
					//already must have been commonlast
					if (preExisting->rt_entry_infos.rtu_router.interfaceAddr.ipv4 == list_destination_n->destination->rt_entry_infos.rtu_router.interfaceAddr.ipv4
						&& preExisting->rt_metric == list_destination_n->destination->rt_metric + 1)
					{
						//consider this as the entry already be added into the n_1 table,
						//since the exchange function may cause lasthop change, so update again will cause the disappear of further update and cause problem.
						//and the exchange means it has already be added to lists, so add again will cause problem as well
						
						preExisting = NULL;
					}							
				}
				


				if (NULL != preExisting)
				{

					preExisting->rt_entry_infos.bCostChanged = FALSE;
					preExisting->rt_entry_infos.bDescendentRequireFurtherUpdate = FALSE;
					preExisting->rt_entry_infos.bRequireDelete = FALSE;

					preExisting->rt_entry_infos.uiCostChg = 0;
					

					if (list_destination_n->destination->rt_entry_infos.bCostChanged)
					{
						//preExisting->rt_entry_infos.bRequireExchange = TRUE;
					
					
						//DebugBreak();
						BOOL bExchangeFound = FindRouteExchangeV21(node,  NULL, preExisting, TRUE, list_destination_n->destination, puiLookupCnt);

						if (!bExchangeFound)
						{

							//this branch should never happen, since the success of find earlier level exchange
							//can ensure there is at least one suitable (maybe not perfect) option
							
							
						}
						else
						{
							if (preExisting->rt_entry_infos.bDescendentRequireFurtherUpdate)
							{

								/*
								if (preExisting->rt_entry_infos.bCostChanged)
								{
									//add to n_2???
									//add to n_1
								}
								else
								{
									//route change 
									//add to n_1???
									//DebugBreak();
									//add to n_0
								
								}
								*/
								
								
							}
							else
							{
								preExisting = NULL;
							}
						}

					}
					else
					{
						//only route changed

						
						//preExisting->rt_entry_infos.bRequireExchange = FALSE;

						//preExisting->rt_entry_infos.bRequireUpdate = TRUE;

						BOOL bExchangeFound = FindRouteExchangeV20(node, NULL, preExisting, TRUE, puiLookupCnt);

						if (bExchangeFound)
						{
							if (preExisting->rt_entry_infos.bDescendentRequireFurtherUpdate)
							{
								//only route change in this case
								//add to n_1???
								//add to n_1
							}
							else
							{
								preExisting = NULL;
							}

						}
						else
						{
							//will never happen
						}

					}		

					
				
					
					bExist = true;
				}
				else
				{
					bExist = false;
				}

			}
			else
			{
				bExist = false;
			}
			
		}
				

		if (bExist && preExisting != NULL)
		{

			// PRINT OUT: Last Hop to Final Destination. The
			// function convert_address_to_string has to be
			// separately

			if (DEBUG)
			{
				char addrString[MAX_STRING_LENGTH];
				IO_ConvertIpAddressToString(
					&list_destination_n->destination->rt_dst,
					addrString);

				printf("%s -> ", addrString);

				IO_ConvertIpAddressToString(
					&addrReached,
					addrString);

				printf("%s\n", addrString);
			}

			destination_n* destination_n_1 = NULL;

			rt_entry* tmp = NULL;

			
			if (preExisting->rt_entry_infos.bDescendentRequireFurtherUpdate)
			{
				
				tmp = preExisting;
			}				
				
			
			// insert in routing table using topology
			if (tmp != NULL)
			{
				destination_n_1 = (destination_n *)
					MEM_malloc(sizeof(destination_n));

				memset(destination_n_1, 0, sizeof(destination_n));

				destination_n_1->destination = tmp;
			}
			

			if (destination_n_1 != NULL)
			{
				
				//!!! in this function, cost change mean only cost plus one change 
				
				//Peter comment: add the new added entry to p_list_destination_n_0 or p_list_destination_n_1
				BOOL bLastHopCostChg = list_destination_n->destination->rt_entry_infos.bCostChanged;

				if (bLastHopCostChg)
				{
					if (preExisting->rt_entry_infos.bCostChanged)
					{
						//add to p_list_destination_n_1
						destination_n_1->next = *p_list_destination_n_1;
						*p_list_destination_n_1 = destination_n_1;
					}
					else
					{
						//DebugBreak();
						
						//add to p_list_destination_n_0, the current list, so it is tricky
						destination_n* destination_n_tmp = NULL;
						destination_n_tmp = (*p_list_destination_n_0)->next;
						destination_n_1->next = destination_n_tmp;
						(*p_list_destination_n_0)->next = destination_n_1;
						
						//*p_list_destination_n_0 = destination_n_1;

					}
				}
				else
				{
					if (preExisting->rt_entry_infos.bCostChanged)
					{
						//impossible
					}
					else
					{
						//add to p_list_destination_n_1
						destination_n_1->next = *p_list_destination_n_1;
						*p_list_destination_n_1 = destination_n_1;
					}
				}

				
				/*
				if (preExisting->rt_entry_infos.bCostChanged)
				{
					
					destination_n_1->next = *p_list_destination_n_2;
					*p_list_destination_n_2 = destination_n_1;

				}
				else
				{
					destination_n_1->next = *p_list_destination_n_1;
					*p_list_destination_n_1 = destination_n_1;
				}
				*/
				
			}
		}
		tmp_addrsp = tmp_addrsp->next_alias;
	}
}


static void OlsrCalculateRoutingTableForSinglePathTopologySearchHelpFuncV20(Node * node, Address addrReached, destination_n* list_destination_n, destination_n** p_list_destination_n_1, UInt32 * puiLookupCnt = NULL)
{

	mid_address tmp_addrs;
	memset( &tmp_addrs, 0, sizeof(mid_address));
	mid_address* tmp_addrsp;

	tmp_addrs.alias = addrReached;


	tmp_addrs.next_alias = OlsrLookupMidAliases(node, addrReached);
	tmp_addrsp = &tmp_addrs;

	while (tmp_addrsp != NULL)
	{

		// topo_dest is not in the routing table

		//Peter Modified and added to support olsr multi-path
		bool bExist = false;
		RouteEntryType ret = NOT_ALLOWED;


		double dDistance = 0.0;
		double dRWON = 0.0;


		if (_OLSR_MULTIPATH)
		{
			if (_TEST_TIME_COMPLEXITY)
			{

				dRWON = list_destination_n->destination->rt_entry_infos.related_neighbor->neighbor_infos.dDegreeWRTNode;
				dDistance = list_destination_n->destination->rt_entry_infos.related_neighbor->neighbor_infos.dDistanceWRTNode;
			}
			else
			{

				dRWON = ComputeRouterDegreeWRTOriginNode(node, list_destination_n->destination->rt_entry_infos.rtu_router.interfaceAddr.ipv4, &dDistance);
				dRWON = SimulateLocalDirectionOfAoA(node, dRWON);
			}
		}
		


		rt_entry* preExisting = NULL;

		//bAdvanced: for optimized accumulative route re-calculation
		
		if (g_iAccumulativeRouteCalculation == 1)
		{

			if (NULL != OlsrLookupRoutingTable(node, tmp_addrsp->alias))
			{

				bExist = true;
			}
		}
		else	//g_iAccumulativeRouteCalculation == 2
		{
		

			if (list_destination_n->destination->rt_entry_infos.bDescendentRequireFurtherUpdate)
			{

					//printf("call OlsrLookupRoutingTableAdvForLastReplace \n");
				//???
				//rt_entry* preConcludeFirst = NULL;
				preExisting = OlsrLookupRoutingTableAdvForLastReplace(node, tmp_addrsp->alias, list_destination_n->destination->rt_dst, 
					list_destination_n->destination->rt_router, list_destination_n->destination->rt_metric + 1, TRUE);

				
				if (NULL != preExisting)
				{

					preExisting->rt_entry_infos.bCostChanged = FALSE;
					preExisting->rt_entry_infos.bDescendentRequireFurtherUpdate = FALSE;
					preExisting->rt_entry_infos.bRequireDelete = FALSE;
					preExisting->rt_entry_infos.uiCostChg = 0;
				

					/*
					if (list_destination_n->destination->rt_entry_infos.bCostChanged)
					{
						//preExisting->rt_entry_infos.bRequireExchange = TRUE;
					
					
						//DebugBreak();
						BOOL bExchangeFound = FindRouteExchangeV20(node, preExisting, TRUE, puiLookupCnt);

						if (!bExchangeFound)
						{

							//this branch should never happen, since the success of find earlier level exchange
							//can ensure there is at least one suitable (maybe not perfect) option
							
							
							//OlsrDeleteRoutingTable(preExisting);
							//preExisting = NULL;

							//*pbRequireRediscovery = TRUE;
							//return NULL;
						}

					}
					else
					*/
					{
						//only route changed

						
						//preExisting->rt_entry_infos.bRequireExchange = FALSE;

						//preExisting->rt_entry_infos.bRequireUpdate = TRUE;

						BOOL bExchangeFound = FindRouteExchangeV20(node, NULL, preExisting, TRUE, puiLookupCnt);

						if (bExchangeFound)
						{
							if (preExisting->rt_entry_infos.bDescendentRequireFurtherUpdate)
							{

							}
							else
							{
								preExisting = NULL;
							}

						}
						else
						{
							//will never happen
						}


					}		

					
					
					
					bExist = true;
				}
				else
				{
					bExist = false;
				}

			}
			else
			{
				bExist = false;
			}

			
		}
		
		

		if (bExist && preExisting != NULL)
		{

			// PRINT OUT: Last Hop to Final Destination. The
			// function convert_address_to_string has to be
			// separately

			if (DEBUG)
			{
				char addrString[MAX_STRING_LENGTH];
				IO_ConvertIpAddressToString(
					&list_destination_n->destination->rt_dst,
					addrString);

				printf("%s -> ", addrString);

				IO_ConvertIpAddressToString(
					&addrReached,
					addrString);

				printf("%s\n", addrString);
			}

			destination_n* destination_n_1 = NULL;

			rt_entry* tmp = NULL;

			
			if (preExisting->rt_entry_infos.bDescendentRequireFurtherUpdate)
			{
				
				tmp = preExisting;
			}				
						

			// insert in routing table using topology
			if (tmp != NULL)
			{
				destination_n_1 = (destination_n *)
					MEM_malloc(sizeof(destination_n));

				memset(destination_n_1, 0, sizeof(destination_n));


				destination_n_1->destination = tmp;
			}
		
			if (destination_n_1!= NULL)
			{
				//Peter comment: add the new added entry to list_destination_n_1
				destination_n_1->next = *p_list_destination_n_1;
				*p_list_destination_n_1 = destination_n_1;
			}
		}
		tmp_addrsp = tmp_addrsp->next_alias;
	}
}




// Peter Add for Specifically support _OLSR_MULTIPATH, use 
// both lastTable and DestTable to search
static void OlsrCalculateRoutingTableForMultiPathTopologySearchHelpFunc(Node * node, Address addrReached, destination_n* list_destination_n, destination_n** p_list_destination_n_1, BOOL bAdvanced = FALSE)
{

	mid_address tmp_addrs;
	memset( &tmp_addrs, 0, sizeof(mid_address));
	mid_address* tmp_addrsp;

	tmp_addrs.alias = addrReached;


	tmp_addrs.next_alias = OlsrLookupMidAliases(node, addrReached);
	tmp_addrsp = &tmp_addrs;

	while (tmp_addrsp != NULL)
	{

		// topo_dest is not in the routing table

		//Peter Modified and added to suppoer olsr multipath
		bool bExist = false;
		RouteEntryType ret = NOT_ALLOWED;


		double dDistance = 0.0;
		double dRWON = 0.0;

		if (_TEST_TIME_COMPLEXITY)
		{
			dRWON = list_destination_n->destination->rt_entry_infos.related_neighbor->neighbor_infos.dDegreeWRTNode;
			dDistance = list_destination_n->destination->rt_entry_infos.related_neighbor->neighbor_infos.dDistanceWRTNode;
		}
		else
		{


			dRWON = ComputeRouterDegreeWRTOriginNode(node, list_destination_n->destination->rt_entry_infos.rtu_router.interfaceAddr.ipv4, &dDistance);
			dRWON = SimulateLocalDirectionOfAoA(node, dRWON);
		}

		rt_entry * prte = NULL; 
		
		// Peter Comment: adjust uiHopCountDiff to 2 is quite important for disjoint path.	

		if (bAdvanced)
		{

			


			ret = OlsrAdvancedLookupRoutingTable(node, tmp_addrsp->alias, 
				list_destination_n->destination->rt_router, 
				(UInt16)(list_destination_n->destination->rt_metric + 1), dRWON, 
				_OLSR_TEMP_ROUTES_LIMIT, list_destination_n->destination->rt_dst, TRUE, &prte);
		}
		else
		{

			ret = OlsrAdvancedLookupRoutingTable(node, tmp_addrsp->alias, 
				list_destination_n->destination->rt_router, 
				(UInt16)(list_destination_n->destination->rt_metric + 1), dRWON, 
				_OLSR_TEMP_ROUTES_LIMIT, list_destination_n->destination->rt_dst);

		}
			

		if (ret != NOT_ALLOWED)
		{

			// PRINT OUT: Last Hop to Final Destination. The
			// function convert_address_to_string has to be
			// seperately

			if (DEBUG)
			{
				char addrString[MAX_STRING_LENGTH];
				IO_ConvertIpAddressToString(
					&list_destination_n->destination->rt_dst,
					addrString);

				printf("%s -> ", addrString);

				IO_ConvertIpAddressToString(
					&addrReached,
					addrString);

				printf("%s\n", addrString);
			}


			if (bAdvanced)
			{
				
				if (prte != NULL)
				{
					//update
					destination_n* destination_n_1 = NULL;

					// changed by SRD for multiple iface problem
					rt_entry* tmp = prte;
						

					// Peter Comment: For new entry with cost larger than exist one,
					// add to routing table, but not to work set
					/*
					if (ret == ALLOWED_BUT_NOT_TO_WORKING_SET)
					{
						tmp = NULL;
					}
					*/

					// insert in routing table using topology
					if (tmp != NULL)
					{

						destination_n_1 = (destination_n *)
							MEM_malloc(sizeof(destination_n));

						memset(destination_n_1, 0, sizeof(destination_n));

						destination_n_1->destination = tmp;
					}
					

					if (destination_n_1!= NULL)
					{
						//Peter comment: add the new added entry to list_destination_n_1
						destination_n_1->next = *p_list_destination_n_1;
						*p_list_destination_n_1 = destination_n_1;
					}

				}
				else
				{
					

					destination_n* destination_n_1 = NULL;

					
					// changed by SRD for multiple iface problem
					rt_entry* tmp =
						OlsrInsertRoutingTablefromTopology(
						node,
						list_destination_n->destination,
						tmp_addrsp->alias,
						list_destination_n->destination->rt_dst,
						dRWON, dDistance				
						);

					// Peter Comment: For new entry with cost larger than exist one,
					// add to routing table, but not to work set
					/*
					if (ret == ALLOWED_BUT_NOT_TO_WORKING_SET)
					{
						tmp = NULL;
					}
					*/

					// insert in routing table using topology
					if (tmp != NULL)
					{
						destination_n_1 = (destination_n *)
							MEM_malloc(sizeof(destination_n));

						memset(destination_n_1, 0, sizeof(destination_n));


						destination_n_1->destination = tmp;
					}
					

					if (destination_n_1!= NULL)
					{
						//Peter comment: add the new added entry to list_destination_n_1
						destination_n_1->next = *p_list_destination_n_1;
						*p_list_destination_n_1 = destination_n_1;
					}

				}

			}
			else
			{
				destination_n* destination_n_1 = NULL;

				// changed by SRD for multiple iface problem
				rt_entry* tmp =
					OlsrInsertRoutingTablefromTopology(
					node,
					list_destination_n->destination,
					tmp_addrsp->alias,
					list_destination_n->destination->rt_dst,
					dRWON, dDistance				
					);

				// Peter Comment: For new entry with cost larger than exist one,
				// add to routing table, but not to work set
				/*
				if (ret == ALLOWED_BUT_NOT_TO_WORKING_SET)
				{
					tmp = NULL;
				}
				*/

				// insert in routing table using topology
				if (tmp != NULL)
				{

					destination_n_1 = (destination_n *)
						MEM_malloc(sizeof(destination_n));

					memset(destination_n_1, 0, sizeof(destination_n));

					destination_n_1->destination = tmp;
				}
				
				if (destination_n_1 != NULL)
				{
					//Peter comment: add the new added entry to list_destination_n_1
					destination_n_1->next = *p_list_destination_n_1;
					*p_list_destination_n_1 = destination_n_1;
				}
			}

			
		}
		tmp_addrsp = tmp_addrsp->next_alias;
	}
}


static
void OlsrCalculateRoutingTableForMultiPathAdv(Node *node)
{

	// Peter Add for Specifically support _OLSR_MULTIPATH, use 
	// both lastTable and DestTable to search

	//GenerateCombinedTopologyTable(node);
	//g_iTopologyChgApplyARC++;
	
	tc_trace_item tti;


	if (_TEST_TIME_COMPLEXITY)
	{
		if (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END)
		{

			/*
			sprintf(strTxt, "%s\n", strTxt);

			sprintf(strTxt, "%sOlsrCalculateRoutingTableForMultiPathAdv Start ************************************************* \n", strTxt); 
			*/

			memset(&tti, 0, sizeof(tc_trace_item));
			tti.bIsAdvOrNot = true;
		}
	}

	//For execution time compute

	double dSimTimeStart = 0.0;
	double dRealTimeStart = 0.0;

	double dSimTimeEnd = 0.0;
	double dRealTimeEnd = 0.0;

	double dRealTimeAfter2HopNeighbor = 0.0;



	char timeStr[MAX_STRING_LENGTH];
	TIME_PrintClockInSecond(getSimTime(node), timeStr, node);

	BOOL bTimeConsumptionValidate = FALSE;

	int iSimTime = atoi(timeStr);

	
	
	//if (_TEST_TIME_COMPLEXITY && (node->nodeId == NODE_ID_FOR_TEST_OUTER_ANGLE || node->nodeId == NODE_ID_FOR_TEST_OUTER_EDGE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_ANGLE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_EDGE || node->nodeId == NODE_ID_FOR_TEST_CENTER) && iSimTime > VALID_SIMULATE_CHECK_TIME)
	if (_TEST_TIME_COMPLEXITY && (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END) && iSimTime > VALID_SIMULATE_CHECK_TIME)
	{


		bTimeConsumptionValidate = TRUE;

		char timeStr[MAX_STRING_LENGTH];

		TIME_PrintClockInSecond(getSimTime(node), timeStr, node);

		char timeStr2[MAX_STRING_LENGTH];

		TIME_PrintClockInSecond(EXTERNAL_QueryRealTime(), timeStr2, node);

		dSimTimeStart = atof(timeStr);
		dRealTimeStart = atof(timeStr2);
		//int iSimTime = atoi(timeStr);

		//sprintf(strTxt, "%sOlsrCalculateRoutingTableForMultiPathAdv Start for node %d at time %f and %f: \n", strTxt, node->nodeId, dSimTimeStart, dRealTimeStart);
		tti.dCurrentSimTime = dSimTimeStart;

		//DebugBreak();
	}


	destination_n* list_destination_n = NULL;
	destination_n* list_destination_n_1 = NULL;
	

	RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

	// RFC 3626 Section 10
	// Move routing table
	
	//ACCUMULATIVE_ROUTE_CALC == 1, modify the routing table directly,
	//so backup is not allowed which may cause current routing table become empty
	//OlsrRoutingMirror(node);

	if (DEBUG)
	{
		printf(" Node %d : Printing Routing Table\n", node->nodeId);

		OlsrPrintRoutingTable(olsr->routingtable);

		printf(" Node %d : Printing Mirror Routing Table\n", node->nodeId);

		OlsrPrintRoutingTable(olsr->mirror_table);
	}

	// Step 1 Delete old entries from the table
	// empty previous routing table before creating a new one

	if (DEBUG)
	{
		printf("Empty IP forwarding table\n");
	}


	if (_TEST_TIME_COMPLEXITY)
	{		
	}
	else
	{
		
		//ACCUMULATIVE_ROUTE_CALC == 1
		//NetworkEmptyForwardingTable(node, ROUTING_PROTOCOL_OLSR_INRIA);
	}


	// Step 2 Add One hop neighbors
	if (DEBUG)
	{
		printf("Fill table with neighbors\n");
	}


	//ACCUMULATIVE_ROUTE_CALC == 1
	//OlsrFillRoutingTableWithNeighbors(node);

	if (olsr->dSectorDegree == 0.0)
	{
		//Maybe determined by neighbor density and upbound of the RouteCountThreshold
		//olsr->dSectorDegree = 1.0;
		olsr->dSectorDegree = (double)((double)M_PI) / ((double)(DEGREE_SECTOR_PER_PI));
	}


	if (DEBUG)
	{
		printf("Fill table with two hop neighbors\n");
	}


	RoutingOlsr* olsrTmp = NULL;


	UInt32 uiLookupCntFor2Hop;
	UInt32 uiLookupCntForAddList;

	if (_TEST_TIME_COMPLEXITY)
	{
		uiLookupCntFor2Hop = 0;
		uiLookupCntForAddList = 0;
	}


	// Step 3 Add two hop neighbors

	//ACCUMULATIVE_ROUTE_CALC == 1
	/*
	//if (_TEST_TIME_COMPLEXITY && (node->nodeId == NODE_ID_FOR_TEST_OUTER_ANGLE || node->nodeId == NODE_ID_FOR_TEST_OUTER_EDGE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_ANGLE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_EDGE || node->nodeId == NODE_ID_FOR_TEST_CENTER))
	if (_TEST_TIME_COMPLEXITY && (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END))
	{
		
		list_destination_n_1 = OlsrFillRoutingTableWith2HopNeighbors(node, &uiLookupCntFor2Hop);
	}
	else
	{

		list_destination_n_1 = OlsrFillRoutingTableWith2HopNeighbors(node);
	}
	*/


	if (g_iAccumulativeRouteCalculation == 1)
	{


		list_destination_n_1 = ProcessRoutingTableAccordingToConfidentCost(node, olsr->uiConfidentCost);
	}
	else	//g_iAccumulativeRouteCalculation == 2
	{

		if (olsr->recent_add_list != NULL)
		{


			if (_TEST_TIME_COMPLEXITY && (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END))
			{
				//uiLookupCntForAddList = 0;

				list_destination_n_1  = ProcessRoutingTableAccordingToRecentAddListMP(node, &uiLookupCntForAddList);
			}
			else
			{
				list_destination_n_1  = ProcessRoutingTableAccordingToRecentAddListMP(node);
			}


		}
	}
	

	//?????????????????
	// for multipath adv, since do not need to consider fill neigbor and 2hop neighbos, this part can be commented
 	/*
	if (_TEST_TIME_COMPLEXITY && (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END) && bTimeConsumptionValidate)
	{

		//char timeStr[MAX_STRING_LENGTH];

		//TIME_PrintClockInSecond(getSimTime(node), timeStr, node);

		char timeStr2[MAX_STRING_LENGTH];

		TIME_PrintClockInSecond(EXTERNAL_QueryRealTime(), timeStr2, node);

		//dSimTimeEnd = atof(timeStr);
		dRealTimeAfter2HopNeighbor = atof(timeStr2);


		sprintf(strTxt, "%sOlsrCalculateRoutingTableForMultiPath after 2Hop Neighbor for node %d: at real time %f: \n", strTxt, node->nodeId, dRealTimeAfter2HopNeighbor);

	}
	*/
	

	
	UInt32 uiLookupCnt;


	UInt32 uiLookpCntForDelete = 0;

	if (_TEST_TIME_COMPLEXITY)
	{
		uiLookupCnt = 0;
	}

	
	// Peter Added for support _OLSR_MULTIPATH
	//UInt16 ui_metric_cost_limitation = 3;

	//if (ACCUMULATIVE_ROUTE_CALC == 1)
	{
		//ui_metric_cost_limitation = olsr->uiConfidentCost + 1;
	}

	// Step 3 Add the remaining destinations looking up the topology table
	list_destination_n = list_destination_n_1;

	while (list_destination_n_1 != NULL)
	{
		list_destination_n_1 = NULL;

		//Peter comment: every loop add group of destination nodes that one hop more from the source node,
		//compare to the group in the previous loop  
		while (list_destination_n != NULL)
		{
			destination_n* destination_n_1 = NULL;

			if (DEBUG)
			{
				char addrString[MAX_STRING_LENGTH];

				IO_ConvertIpAddressToString(
					&list_destination_n->destination->rt_dst,
					addrString);

				printf("Node %d, Last hop %s\n",
					node->nodeId,
					addrString);
			}



			/*
			topology_destination_entry* topo_dest_ForCombinedTable;
			last_list *list_of_last_ForCombinedTable;


			if (NULL != (topo_dest_ForCombinedTable = OlsrLookupCombinedTopologyTable(
				node, list_destination_n->destination->rt_dst)))
			{

				list_of_last_ForCombinedTable = topo_dest_ForCombinedTable->topology_destination_list_of_last;

				while (list_of_last_ForCombinedTable != NULL)
				{

					//Address addrReached;
					//SetIPv4AddressInfo(&addrReached, list_of_last_ForDestTable->last_neighbor->topologylast_hash);
					
					if (RoutingOlsrCheckMyIfaceAddress(
						node,
						list_of_last_ForCombinedTable->last_neighbor->topology_last) != -1)
					{
						list_of_last_ForCombinedTable = list_of_last_ForCombinedTable->next;
						continue;
					}

					OlsrCalculateRoutingTableForMultiPathTopologySearchHelpFunc(node, list_of_last_ForCombinedTable->last_neighbor->topology_last, list_destination_n, &list_destination_n_1);

					list_of_last_ForCombinedTable = list_of_last_ForCombinedTable->next;
				}
			}
			*/
			
			
			if (SYMMETRIC_TOPOLOGY_TABLE)
			{
			
				//Peter comment: Original last topology table as well 
				topology_last_entry* topo_last;
				destination_list* topo_dest;

				if (NULL != (topo_last = OlsrLookupLastTopologyTableSYM(
					node, list_destination_n->destination->rt_dst)))
				{
					topo_dest = topo_last->topology_list_of_destinations;
				

					while (topo_dest != NULL)
					{
						
						Address addrReached = topo_dest->destination_node->topology_destination_dst;

						if (RoutingOlsrCheckMyIfaceAddress(
							node,
							addrReached) != -1)
						{
							topo_dest = topo_dest->next;
							continue;
						}

						OlsrCalculateRoutingTableForMultiPathTopologySearchHelpFunc(node, addrReached, list_destination_n, &list_destination_n_1, TRUE);
					

						//Peter Added for test time complexity
						if (_TEST_TIME_COMPLEXITY)
						{

							//if (node->nodeId == NODE_ID_FOR_TEST_OUTER_ANGLE || node->nodeId == NODE_ID_FOR_TEST_OUTER_EDGE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_ANGLE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_EDGE || node->nodeId == NODE_ID_FOR_TEST_CENTER)
							if (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END)
							{
								uiLookupCnt++;
							}
						}


						topo_dest = topo_dest->next;
					}
				}
			}
			else
			{
				//Peter comment: find from the topology table if there is some entry 
				//whose last hop equal the specific dest hop of 2 or more (* since every loop will
				// increase the one more hop count) hop neighbors
				
				//Peter comment: add to use dest topology table as well 
				topology_destination_entry* topo_dest_ForDestTable;
				last_list *list_of_last_ForDestTable;

				
				if (NULL != (topo_dest_ForDestTable = OlsrLookupDestTopologyTable(
					node, list_destination_n->destination->rt_dst)))
				{
					
					list_of_last_ForDestTable = topo_dest_ForDestTable->topology_destination_list_of_last;

					while (list_of_last_ForDestTable != NULL)
					{
						
						Address addrReached;
						SetIPv4AddressInfo(&addrReached, list_of_last_ForDestTable->last_neighbor->topologylast_hash);

						if (RoutingOlsrCheckMyIfaceAddress(
							node,
							addrReached) != -1)
						{
							list_of_last_ForDestTable = list_of_last_ForDestTable->next;
							continue;
						}

						OlsrCalculateRoutingTableForMultiPathTopologySearchHelpFunc(node, addrReached, list_destination_n, &list_destination_n_1);
						

						//Peter Added for test time complexity
						if (_TEST_TIME_COMPLEXITY)
						{

							//if (node->nodeId == NODE_ID_FOR_TEST_OUTER_ANGLE || node->nodeId == NODE_ID_FOR_TEST_OUTER_EDGE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_ANGLE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_EDGE || node->nodeId == NODE_ID_FOR_TEST_CENTER)
							if (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END)
							{
								uiLookupCnt++;

							}
						}

						list_of_last_ForDestTable = list_of_last_ForDestTable->next;
					}
				}
				
				//Peter comment: Original last topology table as well 
				topology_last_entry* topo_last;
				destination_list* topo_dest;

				if (NULL != (topo_last = OlsrLookupLastTopologyTable(
					node, list_destination_n->destination->rt_dst)))
				{
					topo_dest = topo_last->topology_list_of_destinations;
				

					while (topo_dest != NULL)
					{

						
						Address addrReached = topo_dest->destination_node->topology_destination_dst;

						if (RoutingOlsrCheckMyIfaceAddress(
							node,
							addrReached) != -1)
						{
							topo_dest = topo_dest->next;
							continue;
						}

						OlsrCalculateRoutingTableForMultiPathTopologySearchHelpFunc(node, addrReached, list_destination_n, &list_destination_n_1);
					

						//Peter Added for test time complexity
						if (_TEST_TIME_COMPLEXITY)
						{

							if (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END)
							{
								uiLookupCnt++;
							}
						}


						topo_dest = topo_dest->next;
					}
				}
			}


			destination_n_1 = list_destination_n;
			list_destination_n = list_destination_n->next;
			MEM_free(destination_n_1);
		}

		list_destination_n = list_destination_n_1;
		//ui_metric_cost_limitation++;
	}

	if (DEBUG)
	{
		printf(" Node %d : Printing Routing Table\n", node->nodeId);
		OlsrPrintRoutingTable(olsr->routingtable);

		printf(" Node %d : Printing Mirror Routing Table\n", node->nodeId);
		OlsrPrintRoutingTable(olsr->mirror_table);
	}



	//for delete list


	if (g_iAccumulativeRouteCalculation == 1)
	{

	}
	else	//g_iAccumulativeRouteCalculation == 2
	{
		if (olsr->recent_delete_list != NULL)
		{



			topology_last_entry* topo_last;
			destination_list* topo_dest;
			//printf("OlsrCalculateRoutingTableAdv stage #2.1 \n");

			BOOL bRequiredRediscovery = FALSE;

			
			if (FALSE)
				//if (node->nodeId == 75 && olsr->naRecentChangedAddressByTC == 65)
				//if (node->nodeId == 75)
			{

				printf("olsr->naRecentChangedAddressByTC = %d \n",olsr->naRecentChangedAddressByTC);

				OlsrPrintNeighborTable(node);

				printf("\n");

				OlsrPrint2HopNeighborTable(node);

				printf("\n");

				OlsrPrintTopologyTable(node);

				printf("\n");


				OlsrPrintDestTopologyTable(node);


				printf("\n");

				OlsrPrintTopologyTableSYM(node);


				printf("\n");
				//if (olsr->recent_add_list != NULL)
				{
					OlsrPrintRoutingTable(olsr->routingtable);
				}

				printf("\n");


				//DebugBreak();
			}
			


			list_destination_n_1  = ProcessRoutingTableAccordingToRecentDeleteListMP(node, &bRequiredRediscovery, &uiLookpCntForDelete);

			//printf("OlsrCalculateRoutingTableAdv stage #2.2 \n");

			if (list_destination_n_1 != NULL)
			{

				//DebugBreak();

				//printf("OlsrCalculateRoutingTableAdv stage #2.2.1 \n");

				
				//do update WRT to lasthop for this case
				list_destination_n = list_destination_n_1;

				while (list_destination_n_1 != NULL)
				{
					list_destination_n_1 = NULL;

					destination_n* tmp_destination_tail = NULL;

					//Peter comment: every loop add group of destination nodes that one hop more from the source node,
					//compare to the group in the previous loop  
					while (list_destination_n != NULL)
					{
						destination_n* destination_n_1 = NULL;

						if (DEBUG)
						{
							char addrString[MAX_STRING_LENGTH];

							IO_ConvertIpAddressToString(
								&list_destination_n->destination->rt_dst,
								addrString);

							printf("Node %d, Last hop %s\n",
								node->nodeId,
								addrString);
						}


						//Peter comment: find from the topology table if there is some entry 
						//whose last hop equal the specific dest hop of 2 or more (* since every loop will
						// increase the one more hop count) hop neighbors
						if (SYMMETRIC_TOPOLOGY_TABLE)
						{
							topo_last = OlsrLookupLastTopologyTableSYM(node, list_destination_n->destination->rt_dst);
						}
						else
						{
							topo_last = OlsrLookupLastTopologyTable(node, list_destination_n->destination->rt_dst);
						}


						if (NULL != topo_last)
						{
							topo_dest = topo_last->topology_list_of_destinations;

							while (topo_dest != NULL)
							{

								Address addrReached = topo_dest->destination_node->topology_destination_dst;

								if (RoutingOlsrCheckMyIfaceAddress(
									node,
									topo_dest->destination_node->topology_destination_dst) != -1)
								{
									topo_dest = topo_dest->next;
									continue;
								}


								UInt32 uiInnerExchangeLUCnt = 0;
								//BOOL bRediscovery = FALSE;
								OlsrCalculateRoutingTableForSinglePathTopologySearchHelpFunc(node, addrReached, list_destination_n, &list_destination_n_1, &tmp_destination_tail, TRUE, TRUE, TRUE, &uiInnerExchangeLUCnt, TRUE, &bRequiredRediscovery);


								//Peter Added for test time complexity
								if (_TEST_TIME_COMPLEXITY)
								{
									uiLookupCnt += uiInnerExchangeLUCnt;

									//if (node->nodeId == NODE_ID_FOR_TEST_OUTER_ANGLE || node->nodeId == NODE_ID_FOR_TEST_OUTER_EDGE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_ANGLE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_EDGE || node->nodeId == NODE_ID_FOR_TEST_CENTER)
									if (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END)
									{
										uiLookupCnt++;

									}
								}

								if (bRequiredRediscovery)
								{
									while (list_destination_n != NULL) 
									{

										destination_n* destination_n_1_tmp = list_destination_n;
										list_destination_n = list_destination_n->next;
										MEM_free(destination_n_1_tmp);
									}

									break;
								}

								topo_dest = topo_dest->next;
							}

							if (bRequiredRediscovery)
							{
								break;
							}
						}

						destination_n_1 = list_destination_n;
						list_destination_n = list_destination_n->next;
						MEM_free(destination_n_1);
					}

					

					list_destination_n = list_destination_n_1;
					//ui_metric_cost_limitation++;

					//bFirstRound = FALSE;

					if (bRequiredRediscovery)
					{

						//DebugBreak();

						while (list_destination_n != NULL) 
						{

							//DebugBreak();

							destination_n* destination_n_1_tmpp = list_destination_n;
							list_destination_n = list_destination_n->next;
							MEM_free(destination_n_1_tmpp);
						}

						list_destination_n = NULL;

						break;

					}
				}


				if (bRequiredRediscovery)
				{
					/*

					DebugBreak();
					while (list_destination_n != NULL) 
					{

						destination_n* destination_n_1 = list_destination_n;
						list_destination_n = list_destination_n->next;
						MEM_free(destination_n_1);
					}

					list_destination_n = NULL;

					*/
					//printf("OlsrCalculateRoutingTableAdv stage #2.2.1.1 \n");

					OlsrCalculateRoutingTableForMultiPath(node, TRUE, &uiLookpCntForDelete);

				}
				else
				{
					//printf("OlsrCalculateRoutingTableAdv stage #2.2.1.2 \n");
				}

				//printf("OlsrCalculateRoutingTableAdv stage #2.2.2 \n");
			}
			else
			{

				//printf("OlsrCalculateRoutingTableAdv stage #2.2.3 \n");

				if (bRequiredRediscovery)
				{

					//printf("OlsrCalculateRoutingTableAdv stage #2.2.3.1 \n");

					OlsrCalculateRoutingTableForMultiPath(node, TRUE, &uiLookpCntForDelete);

					//BOOL bDisableTimeEstimate = FALSE, UInt32 * uiTotalLookupCnt = NULL
					
					
					//OlsrCalculateRoutingTable
				}
				else
				{
					//do nothing here, since it is possible that there is no other node nearby the deleted node,
					//or every neighbor can find perfect nodes for replace.

					//printf("OlsrCalculateRoutingTableAdv stage #2.2.3.2 \n");
				}

				//already have done by OlsrCalculateRoutingTable version
				//printf("OlsrCalculateRoutingTableAdv stage #2.2.4 \n");
			}


			//printf("OlsrCalculateRoutingTableAdv stage #2.4 \n");
		}
	}
	



	OlsrInsertRoutingTableFromHnaTable(node);

	OlsrReleaseRoutingTable(olsr->mirror_table);


	
	//if (_TEST_TIME_COMPLEXITY && (node->nodeId == NODE_ID_FOR_TEST_OUTER_ANGLE || node->nodeId == NODE_ID_FOR_TEST_OUTER_EDGE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_ANGLE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_EDGE || node->nodeId == NODE_ID_FOR_TEST_CENTER) && bTimeConsumptionValidate)
	if (_TEST_TIME_COMPLEXITY && (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END) && bTimeConsumptionValidate)
	{

		char timeStr[MAX_STRING_LENGTH];

		TIME_PrintClockInSecond(getSimTime(node), timeStr, node);

		char timeStr2[MAX_STRING_LENGTH];

		TIME_PrintClockInSecond(EXTERNAL_QueryRealTime(), timeStr2, node);

		dSimTimeEnd = atof(timeStr);
		dRealTimeEnd = atof(timeStr2);
		//int iSimTime = atoi(timeStr);

		/*
		sprintf(strTxt, "%sOlsrCalculateRoutingTableForMultiPathAdv End for node %d at time %f and %f: \n", strTxt, node->nodeId, dSimTimeEnd, dRealTimeEnd);


		sprintf(strTxt, "%sOlsrCalculateRoutingTableForMultiPathAdv Time consumption for node %d: real_time = %f \n", strTxt, node->nodeId, 
			(double)((dRealTimeEnd - dRealTimeStart) / (double) 2.0));
		*/

		if (SYMMETRIC_TOPOLOGY_TABLE)
		{
			tti.dRealTimeDuration = dRealTimeEnd - dRealTimeStart;
		}
		else
		{
			tti.dRealTimeDuration = (double)((dRealTimeEnd - dRealTimeStart) / (double) 2.0);
		}
		

	}


	if (_TEST_TIME_COMPLEXITY)
	{

		//if (node->nodeId == NODE_ID_FOR_TEST_OUTER_ANGLE || node->nodeId == NODE_ID_FOR_TEST_OUTER_EDGE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_ANGLE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_EDGE || node->nodeId == NODE_ID_FOR_TEST_CENTER)
		if (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END)
		{
			/*
			sprintf(strTxt, "%sOlsrCalculateRoutingTableForMultiPathAdv End : uiLookupCnt = %d, uiLookupCntFor2Hop = %d ******************************* \n", strTxt, uiLookupCnt, uiLookupCntFor2Hop); 
			sprintf(strTxt, "%sOlsrCalculateRoutingTableForMultiPathAdv Combiled Count for node %d: CombiledCnt = %d ******************************* \n\n", strTxt, node->nodeId, (uiLookupCnt / 2) + uiLookupCntFor2Hop); 
			*/

			//uiLookupCntFor2Hop == 0

			
			if (SYMMETRIC_TOPOLOGY_TABLE)
			{
				//tti.iCombinedCnt = uiLookupCnt + uiLookupCntFor2Hop;

				tti.iCombinedCnt = uiLookupCnt + uiLookupCntFor2Hop;

				if (g_iAccumulativeRouteCalculation == 1)
				{
				}
				else
				{

					tti.iCombinedCnt += uiLookpCntForDelete;
					
					tti.iCombinedCnt += uiLookupCntForAddList;

					/*
					if (uiLookupCntForAddList != 0)
					{
						DebugBreak();
					}
					*/
				}
			}
			else
			{
				tti.iCombinedCnt = (uiLookupCnt / 2) + uiLookupCntFor2Hop;
			}
			


			

			PUSH_BACK_CURRENT_ITEM(olsr, tti);
		}

	}
}


static
void OlsrCalculateRoutingTableForMultiPath(Node *node, BOOL bDisableTimeEstimate, UInt32 * uiTotalLookupCnt)
{

	// Peter Add for Specifically support _OLSR_MULTIPATH, use 
	// both lastTable and DestTable to search

	//GenerateCombinedTopologyTable(node);

	/*
	char strTxt[2048];
	memset(strTxt, 0, 2048 * sizeof(char));
	*/

	tc_trace_item tti;

	if (!bDisableTimeEstimate && _TEST_TIME_COMPLEXITY)
	{
		if (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END)
		//if (node->nodeId == NODE_ID_FOR_TEST_OUTER_ANGLE || node->nodeId == NODE_ID_FOR_TEST_OUTER_EDGE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_ANGLE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_EDGE || node->nodeId == NODE_ID_FOR_TEST_CENTER)
		{

			/*
			sprintf(strTxt, "%s\n", strTxt);

			sprintf(strTxt, "%sOlsrCalculateRoutingTableForMultiPath Start ************************************************* \n", strTxt); 
			*/
			memset(&tti, 0, sizeof(tc_trace_item));
			tti.bIsAdvOrNot = false;
		}
	}

	//For execution time compute

	double dSimTimeStart = 0.0;
	double dRealTimeStart = 0.0;

	double dSimTimeEnd = 0.0;
	double dRealTimeEnd = 0.0;

	double dRealTimeAfter2HopNeighbor = 0.0;



	char timeStr[MAX_STRING_LENGTH];
	TIME_PrintClockInSecond(getSimTime(node), timeStr, node);

	BOOL bTimeConsumptionValidate = FALSE;

	int iSimTime = atoi(timeStr);

	
	
	//if (_TEST_TIME_COMPLEXITY && (node->nodeId == NODE_ID_FOR_TEST_OUTER_ANGLE || node->nodeId == NODE_ID_FOR_TEST_OUTER_EDGE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_ANGLE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_EDGE || node->nodeId == NODE_ID_FOR_TEST_CENTER) && iSimTime > VALID_SIMULATE_CHECK_TIME)
	if (!bDisableTimeEstimate && _TEST_TIME_COMPLEXITY && (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END) && iSimTime > VALID_SIMULATE_CHECK_TIME)
	{


		bTimeConsumptionValidate = TRUE;

		char timeStr[MAX_STRING_LENGTH];

		TIME_PrintClockInSecond(getSimTime(node), timeStr, node);

		char timeStr2[MAX_STRING_LENGTH];

		TIME_PrintClockInSecond(EXTERNAL_QueryRealTime(), timeStr2, node);

		dSimTimeStart = atof(timeStr);
		dRealTimeStart = atof(timeStr2);
		//int iSimTime = atoi(timeStr);

		//sprintf(strTxt, "%sOlsrCalculateRoutingTableForMultiPath Start for node %d at time %f and %f: \n", strTxt, node->nodeId, dSimTimeStart, dRealTimeStart);

		tti.dCurrentSimTime = dSimTimeStart;

		//DebugBreak();
	}


	destination_n* list_destination_n = NULL;
	destination_n* list_destination_n_1 = NULL;
	

	RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

	// RFC 3626 Section 10
	// Move routing table
	OlsrRoutingMirror(node);

	if (DEBUG)
	{
		printf(" Node %d : Printing Routing Table\n", node->nodeId);

		OlsrPrintRoutingTable(olsr->routingtable);

		printf(" Node %d : Printing Mirror Routing Table\n", node->nodeId);

		OlsrPrintRoutingTable(olsr->mirror_table);
	}

	// Step 1 Delete old entries from the table
	// empty previous routing table before creating a new one

	if (DEBUG)
	{
		printf("Empty IP forwarding table\n");
	}


	if (_TEST_TIME_COMPLEXITY)
	{		
	}
	else
	{

		NetworkEmptyForwardingTable(node, ROUTING_PROTOCOL_OLSR_INRIA);
	}


	// Step 2 Add One hop neighbors
	if (DEBUG)
	{
		printf("Fill table with neighbors\n");
	}



	OlsrFillRoutingTableWithNeighbors(node);

	if (olsr->dSectorDegree == 0.0)
	{
		//Maybe determined by neighbor density and upbound of the RouteCountThreshold
		//olsr->dSectorDegree = 1.0;
		olsr->dSectorDegree = (double)((double)M_PI) / ((double)(DEGREE_SECTOR_PER_PI));
	}


	if (DEBUG)
	{
		printf("Fill table with two hop neighbors\n");
	}


	RoutingOlsr* olsrTmp = NULL;


	UInt32 uiLookupCntFor2Hop;

	if (_TEST_TIME_COMPLEXITY)
	{
		uiLookupCntFor2Hop = 0;
	}


	// Step 3 Add two hop neighbors

	
	//if (_TEST_TIME_COMPLEXITY && (node->nodeId == NODE_ID_FOR_TEST_OUTER_ANGLE || node->nodeId == NODE_ID_FOR_TEST_OUTER_EDGE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_ANGLE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_EDGE || node->nodeId == NODE_ID_FOR_TEST_CENTER))
	if (_TEST_TIME_COMPLEXITY && (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END))
	{
		
		list_destination_n_1 = OlsrFillRoutingTableWith2HopNeighbors(node, &uiLookupCntFor2Hop);
	}
	else
	{

		list_destination_n_1 = OlsrFillRoutingTableWith2HopNeighbors(node);
	}
	

	
	//if (_TEST_TIME_COMPLEXITY && (node->nodeId == NODE_ID_FOR_TEST_OUTER_ANGLE || node->nodeId == NODE_ID_FOR_TEST_OUTER_EDGE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_ANGLE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_EDGE || node->nodeId == NODE_ID_FOR_TEST_CENTER) && bTimeConsumptionValidate)
	if (!bDisableTimeEstimate && _TEST_TIME_COMPLEXITY && (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END) && bTimeConsumptionValidate)
	{

		//char timeStr[MAX_STRING_LENGTH];

		//TIME_PrintClockInSecond(getSimTime(node), timeStr, node);

		char timeStr2[MAX_STRING_LENGTH];

		TIME_PrintClockInSecond(EXTERNAL_QueryRealTime(), timeStr2, node);

		//dSimTimeEnd = atof(timeStr);
		dRealTimeAfter2HopNeighbor = atof(timeStr2);


		//sprintf(strTxt, "%sOlsrCalculateRoutingTableForMultiPath after 2Hop Neighbor for node %d: at real time %f: \n", strTxt, node->nodeId, dRealTimeAfter2HopNeighbor);

	}
	


	
	UInt32 uiLookupCnt;

	if (_TEST_TIME_COMPLEXITY)
	{
		uiLookupCnt = 0;
	}


	
	// Peter Added for support _OLSR_MULTIPATH
	//UInt16 ui_metric_cost_limitation = 3;

	// Step 3 Add the remaining destinations looking up the topology table
	list_destination_n = list_destination_n_1;

	while (list_destination_n_1 != NULL)
	{
		list_destination_n_1 = NULL;

		//Peter comment: every loop add group of destination nodes that one hop more from the source node,
		//compare to the group in the previous loop  
		while (list_destination_n != NULL)
		{
			destination_n* destination_n_1 = NULL;

			if (DEBUG)
			{
				char addrString[MAX_STRING_LENGTH];

				IO_ConvertIpAddressToString(
					&list_destination_n->destination->rt_dst,
					addrString);

				printf("Node %d, Last hop %s\n",
					node->nodeId,
					addrString);
			}



			/*
			topology_destination_entry* topo_dest_ForCombinedTable;
			last_list *list_of_last_ForCombinedTable;


			if (NULL != (topo_dest_ForCombinedTable = OlsrLookupCombinedTopologyTable(
				node, list_destination_n->destination->rt_dst)))
			{

				list_of_last_ForCombinedTable = topo_dest_ForCombinedTable->topology_destination_list_of_last;

				while (list_of_last_ForCombinedTable != NULL)
				{

					//Address addrReached;
					//SetIPv4AddressInfo(&addrReached, list_of_last_ForDestTable->last_neighbor->topologylast_hash);
					
					if (RoutingOlsrCheckMyIfaceAddress(
						node,
						list_of_last_ForCombinedTable->last_neighbor->topology_last) != -1)
					{
						list_of_last_ForCombinedTable = list_of_last_ForCombinedTable->next;
						continue;
					}

					OlsrCalculateRoutingTableForMultiPathTopologySearchHelpFunc(node, list_of_last_ForCombinedTable->last_neighbor->topology_last, list_destination_n, &list_destination_n_1);

					list_of_last_ForCombinedTable = list_of_last_ForCombinedTable->next;
				}
			}
			*/
				
			if (SYMMETRIC_TOPOLOGY_TABLE)
			{
				topology_last_entry* topo_last;
				destination_list* topo_dest;

				if (NULL != (topo_last = OlsrLookupLastTopologyTableSYM(
					node, list_destination_n->destination->rt_dst)))
				{
					topo_dest = topo_last->topology_list_of_destinations;


					while (topo_dest != NULL)
					{


						Address addrReached = topo_dest->destination_node->topology_destination_dst;

						if (RoutingOlsrCheckMyIfaceAddress(
							node,
							addrReached) != -1)
						{
							topo_dest = topo_dest->next;
							continue;
						}

						OlsrCalculateRoutingTableForMultiPathTopologySearchHelpFunc(node, addrReached, list_destination_n, &list_destination_n_1);


						//Peter Added for test time complexity
						if (_TEST_TIME_COMPLEXITY)
						{

							//if (node->nodeId == NODE_ID_FOR_TEST_OUTER_ANGLE || node->nodeId == NODE_ID_FOR_TEST_OUTER_EDGE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_ANGLE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_EDGE || node->nodeId == NODE_ID_FOR_TEST_CENTER)
							if (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END)
							{
								uiLookupCnt++;
							}
						}


						topo_dest = topo_dest->next;
					}
				}
			}
			else
			{
				//Peter comment: find from the topology table if there is some entry 
				//whose last hop equal the specific dest hop of 2 or more (* since every loop will
				// increase the one more hop count) hop neighbors

				//Peter comment: add to use dest topology table as well 
				topology_destination_entry* topo_dest_ForDestTable;
				last_list *list_of_last_ForDestTable;


				if (NULL != (topo_dest_ForDestTable = OlsrLookupDestTopologyTable(
					node, list_destination_n->destination->rt_dst)))
				{

					list_of_last_ForDestTable = topo_dest_ForDestTable->topology_destination_list_of_last;

					while (list_of_last_ForDestTable != NULL)
					{

						Address addrReached;
						SetIPv4AddressInfo(&addrReached, list_of_last_ForDestTable->last_neighbor->topologylast_hash);

						if (RoutingOlsrCheckMyIfaceAddress(
							node,
							addrReached) != -1)
						{
							list_of_last_ForDestTable = list_of_last_ForDestTable->next;
							continue;
						}

						OlsrCalculateRoutingTableForMultiPathTopologySearchHelpFunc(node, addrReached, list_destination_n, &list_destination_n_1);


						//Peter Added for test time complexity
						if (_TEST_TIME_COMPLEXITY)
						{

							//if (node->nodeId == NODE_ID_FOR_TEST_OUTER_ANGLE || node->nodeId == NODE_ID_FOR_TEST_OUTER_EDGE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_ANGLE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_EDGE || node->nodeId == NODE_ID_FOR_TEST_CENTER)
							if (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END)
							{
								uiLookupCnt++;

							}
						}

						list_of_last_ForDestTable = list_of_last_ForDestTable->next;
					}
				}


				//SYMMETRIC TOPOLOGY TABLE

				//Peter comment: Original last topology table as well 
				topology_last_entry* topo_last;
				destination_list* topo_dest;

				if (NULL != (topo_last = OlsrLookupLastTopologyTable(
					node, list_destination_n->destination->rt_dst)))
				{
					topo_dest = topo_last->topology_list_of_destinations;


					while (topo_dest != NULL)
					{


						Address addrReached = topo_dest->destination_node->topology_destination_dst;

						if (RoutingOlsrCheckMyIfaceAddress(
							node,
							addrReached) != -1)
						{
							topo_dest = topo_dest->next;
							continue;
						}

						OlsrCalculateRoutingTableForMultiPathTopologySearchHelpFunc(node, addrReached, list_destination_n, &list_destination_n_1);


						//Peter Added for test time complexity
						if (_TEST_TIME_COMPLEXITY)
						{

							//if (node->nodeId == NODE_ID_FOR_TEST_OUTER_ANGLE || node->nodeId == NODE_ID_FOR_TEST_OUTER_EDGE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_ANGLE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_EDGE || node->nodeId == NODE_ID_FOR_TEST_CENTER)
							if (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END)
							{
								uiLookupCnt++;
							}
						}


						topo_dest = topo_dest->next;
					}
				}
			}
			

			destination_n_1 = list_destination_n;
			list_destination_n = list_destination_n->next;
			MEM_free(destination_n_1);
		}

		list_destination_n = list_destination_n_1;
		//ui_metric_cost_limitation++;
	}

	if (DEBUG)
	{
		printf(" Node %d : Printing Routing Table\n", node->nodeId);
		OlsrPrintRoutingTable(olsr->routingtable);

		printf(" Node %d : Printing Mirror Routing Table\n", node->nodeId);
		OlsrPrintRoutingTable(olsr->mirror_table);
	}


	OlsrInsertRoutingTableFromHnaTable(node);

	OlsrReleaseRoutingTable(olsr->mirror_table);


	
	//if (_TEST_TIME_COMPLEXITY && (node->nodeId == NODE_ID_FOR_TEST_OUTER_ANGLE || node->nodeId == NODE_ID_FOR_TEST_OUTER_EDGE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_ANGLE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_EDGE || node->nodeId == NODE_ID_FOR_TEST_CENTER) && bTimeConsumptionValidate)
	if (!bDisableTimeEstimate && _TEST_TIME_COMPLEXITY && (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END) && bTimeConsumptionValidate)
	{

		char timeStr[MAX_STRING_LENGTH];

		TIME_PrintClockInSecond(getSimTime(node), timeStr, node);

		char timeStr2[MAX_STRING_LENGTH];

		TIME_PrintClockInSecond(EXTERNAL_QueryRealTime(), timeStr2, node);

		dSimTimeEnd = atof(timeStr);
		dRealTimeEnd = atof(timeStr2);
		//int iSimTime = atoi(timeStr);

		/*
		sprintf(strTxt, "%sOlsrCalculateRoutingTableForMultiPath End for node %d at time %f and %f: \n", strTxt, node->nodeId, dSimTimeEnd, dRealTimeEnd);


		sprintf(strTxt, "%sOlsrCalculateRoutingTableForMultiPath Time consumption for node %d: real_time = %f \n", strTxt, node->nodeId, 
			(double)((dRealTimeEnd - dRealTimeAfter2HopNeighbor) / (double) 2.0) + (dRealTimeAfter2HopNeighbor - dRealTimeStart));
		*/

		if (SYMMETRIC_TOPOLOGY_TABLE)
		{
			tti.dRealTimeDuration = dRealTimeEnd - dRealTimeStart;
		}
		else
		{
			tti.dRealTimeDuration = (double)((dRealTimeEnd - dRealTimeAfter2HopNeighbor) / (double) 2.0) + (dRealTimeAfter2HopNeighbor - dRealTimeStart);
		}

	}

	if (bDisableTimeEstimate && uiTotalLookupCnt != NULL)
	{
		*uiTotalLookupCnt = uiLookupCnt + uiLookupCntFor2Hop;
	}

	if (!bDisableTimeEstimate && _TEST_TIME_COMPLEXITY)
	{

		//if (node->nodeId == NODE_ID_FOR_TEST_OUTER_ANGLE || node->nodeId == NODE_ID_FOR_TEST_OUTER_EDGE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_ANGLE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_EDGE || node->nodeId == NODE_ID_FOR_TEST_CENTER)
		if (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END)
		{
			/*
			sprintf(strTxt, "%sOlsrCalculateRoutingTableForMultiPath End : uiLookupCnt = %d, uiLookupCntFor2Hop = %d ******************************* \n", strTxt, uiLookupCnt, uiLookupCntFor2Hop); 
			sprintf(strTxt, "%sOlsrCalculateRoutingTableForMultiPath Combiled Count for node %d: CombiledCnt = %d ******************************* \n\n", strTxt, node->nodeId, (uiLookupCnt / 2) + uiLookupCntFor2Hop); 
			*/

			if (SYMMETRIC_TOPOLOGY_TABLE)
			{
				tti.iCombinedCnt = uiLookupCnt + uiLookupCntFor2Hop;
			}
			else
			{
				tti.iCombinedCnt = (uiLookupCnt / 2) + uiLookupCntFor2Hop;
			}
			

			PUSH_BACK_CURRENT_ITEM(olsr, tti);
		}

		//sprintf(g_strTxt, "%s \n %s", g_strTxt, strTxt);

	

	}

}


static
void OlsrCalculateRoutingTable(Node *node, BOOL bDisableTimeEstimate = FALSE, UInt32 * uiTotalLookupCnt = NULL)
{

	

	g_iTopologyChgApplyNormal++;

	//printf("OlsrCalculateRoutingTable for node %d Begin \n", node->nodeId);
	
	/*
	if (node->nodeId == 1)
	{

		printf("OlsrCalculateRoutingTable for node 1 \n");
	}
	*/

	if (g_iTestRCSimAndRealTime == 1)
	{
		
		if (node->nodeId == DEBUG_NODE_ID)
		{
			char timeStr3[MAX_STRING_LENGTH];

			TIME_PrintClockInSecond(getSimTime(node), timeStr3, node);

			char timeStr4[MAX_STRING_LENGTH];

			TIME_PrintClockInSecond(EXTERNAL_QueryRealTime(), timeStr4, node);

			double ddSimTimeStart = atof(timeStr3);
			double ddRealTimeStart = atof(timeStr4);

			//printf("OlsrCalculateRoutingTable start for node No.%d, ddSimTimeStart = %f, ddRealTimeStart = %f \n", 
			//	node->nodeId, ddSimTimeStart, ddRealTimeStart);
		}
	}


	//Peter Adder for test time complexity
	/*
	char strTxt[2048];
	memset(strTxt, 0, 2048 * sizeof(char));
	*/
	tc_trace_item tti;


	if (!bDisableTimeEstimate && _TEST_TIME_COMPLEXITY && g_iSimplifiedTimeTest == 0)
	{
		
		//if (node->nodeId == NODE_ID_FOR_TEST_OUTER_ANGLE || node->nodeId == NODE_ID_FOR_TEST_OUTER_EDGE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_ANGLE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_EDGE || node->nodeId == NODE_ID_FOR_TEST_CENTER)
		if (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END)
		{
			
			
		
			memset(&tti, 0, sizeof(tc_trace_item));
			tti.bIsAdvOrNot = false;
			
		
			
			/*
			sprintf(strTxt, "%s\n", strTxt);

			sprintf(strTxt, "%sOlsrCalculateRoutingTable Start ************************************************* \n", strTxt); 
			*/
		}
	}

	
	
	//For execution time compute
	
	double dSimTimeStart = 0.0;
	double dRealTimeStart = 0.0;

	double dSimTimeEnd = 0.0;
	double dRealTimeEnd = 0.0;
	
	
	
	char timeStr[MAX_STRING_LENGTH];
	TIME_PrintClockInSecond(getSimTime(node), timeStr, node);

	BOOL bTimeConsumptionValidate = FALSE;

	int iSimTime = atoi(timeStr);

	dSimTimeStart = atof(timeStr);
	
	
    //if (_TEST_TIME_COMPLEXITY && (node->nodeId == NODE_ID_FOR_TEST_OUTER_ANGLE || node->nodeId == NODE_ID_FOR_TEST_OUTER_EDGE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_ANGLE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_EDGE || node->nodeId == NODE_ID_FOR_TEST_CENTER) && iSimTime > VALID_SIMULATE_CHECK_TIME)
	if (!bDisableTimeEstimate && _TEST_TIME_COMPLEXITY && (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END) && iSimTime > VALID_SIMULATE_CHECK_TIME)
	{
		
		bTimeConsumptionValidate = TRUE;
		
		if (g_iSimplifiedTimeTest == 1)
		{
			char timeStr2[MAX_STRING_LENGTH];

			TIME_PrintClockInSecond(EXTERNAL_QueryRealTime(), timeStr2, node);

			
			dRealTimeStart = atof(timeStr2);

			

		}
		else
		{
			char timeStr[MAX_STRING_LENGTH];

			TIME_PrintClockInSecond(getSimTime(node), timeStr, node);

			char timeStr2[MAX_STRING_LENGTH];

			TIME_PrintClockInSecond(EXTERNAL_QueryRealTime(), timeStr2, node);

			dSimTimeStart = atof(timeStr);
			dRealTimeStart = atof(timeStr2);
			//int iSimTime = atoi(timeStr);

			//sprintf(strTxt, "%sOlsrCalculateRoutingTable Start for node %d at time %f and %f: \n", strTxt, node->nodeId, dSimTimeStart, dRealTimeStart);

			tti.dCurrentSimTime = dSimTimeStart;
		}
		

				
    }
	
	
	
	
	
	//printf("!!!!!!!!!!!!!!    start OlsrCalculateRoutingTable \n");
	
	destination_n* list_destination_n = NULL;
    destination_n* list_destination_n_1 = NULL;
    topology_last_entry* topo_last;
    destination_list* topo_dest;

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    // RFC 3626 Section 10
    // Move routing table
    OlsrRoutingMirror(node);

    if (DEBUG)
    {
        printf(" Node %d : Printing Routing Table\n", node->nodeId);

        OlsrPrintRoutingTable(olsr->routingtable);

        printf(" Node %d : Printing Mirror Routing Table\n", node->nodeId);

        OlsrPrintRoutingTable(olsr->mirror_table);
    }

    // Step 1 Delete old entries from the table
    // empty previous routing table before creating a new one

    if (DEBUG)
    {
        printf("Empty IP forwarding table\n");
    }


	

	if (_TEST_TIME_COMPLEXITY || FORWARD_WITH_PURE_ROUTE_TABLE)
	{
	}
	else
	{

		NetworkEmptyForwardingTable(node, ROUTING_PROTOCOL_OLSR_INRIA);
	}

    
    // Step 2 Add One hop neighbors
    if (DEBUG)
    {
        printf("Fill table with neighbors\n");
    }



    OlsrFillRoutingTableWithNeighbors(node);


    if (DEBUG)
    {
        printf("Fill table with two hop neighbors\n");
    }


	RoutingOlsr* olsrTmp = NULL;


	/*
	if (node->nodeId == 1)
	{
		printf("node 1 After OlsrFillRoutingTableWithNeighbors: \n");

		olsrTmp = (RoutingOlsr* ) node->appData.olsr;
		OlsrPrintRoutingTable(olsrTmp->routingtable);
	}
	*/


	UInt32 uiLookupCntFor2Hop;

	if (_TEST_TIME_COMPLEXITY)
	{
		uiLookupCntFor2Hop = 0;
	}

    // Step 3 Add two hop neighbors
    
	
	//if (_TEST_TIME_COMPLEXITY && (node->nodeId == NODE_ID_FOR_TEST_OUTER_ANGLE || node->nodeId == NODE_ID_FOR_TEST_OUTER_EDGE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_ANGLE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_EDGE || node->nodeId == NODE_ID_FOR_TEST_CENTER))
	if (_TEST_TIME_COMPLEXITY && g_iSimplifiedTimeTest == 0 && (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END))
	{

		list_destination_n_1 = OlsrFillRoutingTableWith2HopNeighbors(node, &uiLookupCntFor2Hop);
	}
	else
	{

		list_destination_n_1 = OlsrFillRoutingTableWith2HopNeighbors(node);
	}
	
	
	
	
	/*
	if (node->nodeId == 1)
	{
		printf("node 1 After OlsrFillRoutingTableWith2HopNeighbors: \n");


		olsrTmp = (RoutingOlsr* ) node->appData.olsr;
		OlsrPrintRoutingTable(olsrTmp->routingtable);

		OlsrPrintTopologyTable(node);
	}
	*/


	//Peter Adder for test time complexity
	
	UInt32 uiLookupCnt;
	
	if (_TEST_TIME_COMPLEXITY)
	{
		uiLookupCnt = 0;
	}



	// Peter Added for support _OLSR_MULTIPATH
	//UInt16 ui_metric_cost_limitation = 3;

    // Step 3 Add the remaining destinations looking up the topology table
    list_destination_n = list_destination_n_1;

    while (list_destination_n_1 != NULL)
    {
        list_destination_n_1 = NULL;
		destination_n* tmp_destination_tail = NULL;


        //Peter comment: every loop add group of destination nodes that one hop more from the source node,
		//compare to the group in the previous loop  
		while (list_destination_n != NULL)
        {
            destination_n* destination_n_1 = NULL;

            if (DEBUG)
            {
                char addrString[MAX_STRING_LENGTH];

                IO_ConvertIpAddressToString(
                    &list_destination_n->destination->rt_dst,
                    addrString);

                printf("Node %d, Last hop %s\n",
                    node->nodeId,
                    addrString);
            }
			

			//SYMMETRIC TOPOLOGY TABLE

			//Peter comment: find from the topology table if there is some entry 
			//whose last hop equal the specific dest hop of 2 or more (* since every loop will
			// increase the one more hop count) hop neighbors
         	if (SYMMETRIC_TOPOLOGY_TABLE)
			{

				topo_last = OlsrLookupLastTopologyTableSYM(node, list_destination_n->destination->rt_dst);
			}
			else
			{

				topo_last = OlsrLookupLastTopologyTable(node, list_destination_n->destination->rt_dst);
			}

			if (NULL != topo_last)
            {

				topo_dest = topo_last->topology_list_of_destinations;

				//Peter comment: Just For debug
				/*
				if (list_destination_n->destination->rt_entry_infos.rtu_dst.interfaceAddr.ipv4 == 7)
				{
					int sdffs = 21321;

				}
				*/

                while (topo_dest != NULL)
                {

					Address addrReached = topo_dest->destination_node->topology_destination_dst;

                    if (RoutingOlsrCheckMyIfaceAddress(
                            node,
                            topo_dest->destination_node->topology_destination_dst) != -1)
                    {
                        topo_dest = topo_dest->next;
                        continue;
                    }


					OlsrCalculateRoutingTableForSinglePathTopologySearchHelpFunc(node, addrReached, list_destination_n, &list_destination_n_1, &tmp_destination_tail);


					//Peter Added for test time complexity
					if (_TEST_TIME_COMPLEXITY && g_iSimplifiedTimeTest == 0)
					{

						//if (node->nodeId == NODE_ID_FOR_TEST_OUTER_ANGLE || node->nodeId == NODE_ID_FOR_TEST_OUTER_EDGE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_ANGLE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_EDGE || node->nodeId == NODE_ID_FOR_TEST_CENTER)
						if (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END)
						{
							uiLookupCnt++;

						}
					}

                    topo_dest = topo_dest->next;
                }
            }

            destination_n_1 = list_destination_n;
            list_destination_n = list_destination_n->next;
            MEM_free(destination_n_1);
        }

        list_destination_n = list_destination_n_1;
		//ui_metric_cost_limitation++;
    }

    if (DEBUG)
    {
        printf(" Node %d : Printing Routing Table\n", node->nodeId);
        OlsrPrintRoutingTable(olsr->routingtable);

        printf(" Node %d : Printing Mirror Routing Table\n", node->nodeId);
        OlsrPrintRoutingTable(olsr->mirror_table);
    }
    
	
	//Peter Need to check !!!!!!!!!!!!!
	OlsrInsertRoutingTableFromHnaTable(node);



    OlsrReleaseRoutingTable(olsr->mirror_table);


	//printf("!!!!!!!!!!!!!!    end OlsrCalculateRoutingTable \n");

	

	//if (_TEST_TIME_COMPLEXITY && (node->nodeId == NODE_ID_FOR_TEST_OUTER_ANGLE || node->nodeId == NODE_ID_FOR_TEST_OUTER_EDGE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_ANGLE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_EDGE || node->nodeId == NODE_ID_FOR_TEST_CENTER) && bTimeConsumptionValidate)
	if (!bDisableTimeEstimate && _TEST_TIME_COMPLEXITY && (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END) && bTimeConsumptionValidate)
	{


		if (g_iSimplifiedTimeTest == 1)
		{
			char timeStr2[MAX_STRING_LENGTH];

			TIME_PrintClockInSecond(EXTERNAL_QueryRealTime(), timeStr2, node);

		
			dRealTimeEnd = atof(timeStr2);

			double dDuration = dRealTimeEnd - dRealTimeStart;

			olsr->dRCRealRuntime += dDuration;
			
			

			if (dSimTimeStart < olsr->dRecentRCStartTime)
			{
				//printf("|||||||||||||||||=======================OlsrCalculateRoutingTable Start Time Exception =======================|||||||||||||| dSimTimeStart = %f dRecentRCStartTime = %f \n", dSimTimeStart, olsr->dRecentRCStartTime);

				//this will never happen
			}


			double dExpectedEndTime = 0.0;

			if (dSimTimeStart > olsr->dRecentRCStartTime && dSimTimeStart < olsr->dRecentRCEndTime)
			{
				//printf("|||||||||||||||||=======================OlsrCalculateRoutingTable when computing RC TIME=======================|||||||||||||| dRecentRCStartTime = %f dRecentRCEndTime = %f CurrentSimTime = %f \n", olsr->dRecentRCStartTime, olsr->dRecentRCEndTime, dSimTimeStart);
				dExpectedEndTime = olsr->dRecentRCEndTime + dDuration;
			}
			else
			{
				olsr->dRecentRCStartTime = dSimTimeStart;
				dExpectedEndTime = dSimTimeStart + dDuration;
			}



			if (dExpectedEndTime > olsr->dRecentRCEndTime)
			{
				olsr->dRecentRCEndTime = dExpectedEndTime;
			}
			else
			{
				//printf("|||||||||||||||||=======================OlsrCalculateRoutingTable End Time Exception =======================|||||||||||||| dExpectedEndTime = %f dRecentRCEndTime = %f \n", dExpectedEndTime, olsr->dRecentRCEndTime);

			}
			
			
			
			//olsr->dRecentRCEndTime = olsr->dRecentRCStartTime + dDuration;
		

			olsr->uiRCNormalCount++;
		}
		else
		{
			char timeStr[MAX_STRING_LENGTH];

			TIME_PrintClockInSecond(getSimTime(node), timeStr, node);

			char timeStr2[MAX_STRING_LENGTH];

			TIME_PrintClockInSecond(EXTERNAL_QueryRealTime(), timeStr2, node);

			dSimTimeEnd = atof(timeStr);
			dRealTimeEnd = atof(timeStr2);
			//int iSimTime = atoi(timeStr);

			/*
			sprintf(strTxt, "%sOlsrCalculateRoutingTable End for node %d at time %f and %f: \n", strTxt, node->nodeId, dSimTimeEnd, dRealTimeEnd);


			sprintf(strTxt, "%sOlsrCalculateRoutingTable Time consumption for node %d: real_time = %f \n", strTxt, node->nodeId, 
				dRealTimeEnd - dRealTimeStart);
			*/
			tti.dRealTimeDuration = dRealTimeEnd - dRealTimeStart;
		}

		
		//DebugBreak();
	}
	

	if (g_iTestRCSimAndRealTime == 1)
	{

		if (node->nodeId == DEBUG_NODE_ID)
		{
			char timeStr3[MAX_STRING_LENGTH];

			TIME_PrintClockInSecond(getSimTime(node), timeStr3, node);

			char timeStr4[MAX_STRING_LENGTH];

			TIME_PrintClockInSecond(EXTERNAL_QueryRealTime(), timeStr4, node);

			double ddSimTimeStart = atof(timeStr3);
			double ddRealTimeStart = atof(timeStr4);

			//printf("OlsrCalculateRoutingTable end for node No.%d, ddSimTimeStart = %f, ddRealTimeStart = %f \n", 
			//	node->nodeId, ddSimTimeStart, ddRealTimeStart);

			if (ddSimTimeStart > 21 && ddSimTimeStart < 23)
			{
				
				printf("OlsrCalculateRoutingTable end for node No.%d, ddSimTimeStart = %f, ddRealTimeStart = %f \n", 
					node->nodeId, ddSimTimeStart, ddRealTimeStart);

				if (olsr->pszRTWithARC == NULL)
				{
					olsr->pszRTWithARC = new char[RT_SIZE];
				}


				memset(olsr->pszRTWithARC, 0, RT_SIZE * sizeof(char));
				OlsrPrintRoutingTable(olsr->routingtable, olsr->pszRTWithARC);

				printf(olsr->pszRTWithARC);
			}
		}
	}


	//Peter Adder for test time complexity

	if (bDisableTimeEstimate && g_iSimplifiedTimeTest == 0 && uiTotalLookupCnt != NULL)
	{
		*uiTotalLookupCnt = uiLookupCnt + uiLookupCntFor2Hop;
	}
	
	if (!bDisableTimeEstimate && _TEST_TIME_COMPLEXITY && g_iSimplifiedTimeTest == 0)
	{
		
		//if (node->nodeId == NODE_ID_FOR_TEST_OUTER_ANGLE || node->nodeId == NODE_ID_FOR_TEST_OUTER_EDGE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_ANGLE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_EDGE || node->nodeId == NODE_ID_FOR_TEST_CENTER)
		if (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END)
		{
			
			/*
			sprintf(strTxt, "%sOlsrCalculateRoutingTable End : uiLookupCnt = %d, uiLookupCntFor2Hop = %d ******************************* \n", strTxt, uiLookupCnt, uiLookupCntFor2Hop); 
			sprintf(strTxt, "%sOlsrCalculateRoutingTable Combiled Count for node %d: CombiledCnt = %d ******************************* \n\n", strTxt, node->nodeId, uiLookupCnt + uiLookupCntFor2Hop); 
			*/
			tti.iCombinedCnt = uiLookupCnt + uiLookupCntFor2Hop;

			PUSH_BACK_CURRENT_ITEM(olsr, tti);


		}

		//sprintf(g_strTxt, "%s \n %s", g_strTxt, strTxt);

	}


	//printf("OlsrCalculateRoutingTable for node %d End\n", node->nodeId);


}


//for compare, use the mirror table
static
void OlsrCalculateRoutingTableForCompare(Node *node)
{
	
	
	
	//printf("!!!!!!!!!!!!!!    start OlsrCalculateRoutingTable \n");
	
	destination_n* list_destination_n = NULL;
    destination_n* list_destination_n_1 = NULL;
    topology_last_entry* topo_last;
    destination_list* topo_dest;

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    // RFC 3626 Section 10
    // Move routing table
    //OlsrRoutingMirror(node);

	OlsrReleaseRoutingTable(olsr->mirror_table);



    OlsrFillRoutingTableWithNeighbors(node, TRUE);


    if (DEBUG)
    {
        printf("Fill table with two hop neighbors\n");
    }


	RoutingOlsr* olsrTmp = NULL;





	UInt32 uiLookupCntFor2Hop;

	if (_TEST_TIME_COMPLEXITY)
	{
		uiLookupCntFor2Hop = 0;
	}

    // Step 3 Add two hop neighbors
    
	
	//if (_TEST_TIME_COMPLEXITY && (node->nodeId == NODE_ID_FOR_TEST_OUTER_ANGLE || node->nodeId == NODE_ID_FOR_TEST_OUTER_EDGE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_ANGLE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_EDGE || node->nodeId == NODE_ID_FOR_TEST_CENTER))
	if (_TEST_TIME_COMPLEXITY && (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END))
	{

		list_destination_n_1 = OlsrFillRoutingTableWith2HopNeighbors(node, &uiLookupCntFor2Hop, TRUE);
	}
	else
	{

		list_destination_n_1 = OlsrFillRoutingTableWith2HopNeighbors(node, NULL, TRUE);
	}
	


	//Peter Adder for test time complexity
	
	UInt32 uiLookupCnt;
	
	if (_TEST_TIME_COMPLEXITY)
	{
		uiLookupCnt = 0;
	}



	// Peter Added for support _OLSR_MULTIPATH
	//UInt16 ui_metric_cost_limitation = 3;

    // Step 3 Add the remaining destinations looking up the topology table
    list_destination_n = list_destination_n_1;

    while (list_destination_n_1 != NULL)
    {
        list_destination_n_1 = NULL;
		destination_n* tmp_destination_tail = NULL;


        //Peter comment: every loop add group of destination nodes that one hop more from the source node,
		//compare to the group in the previous loop  
		while (list_destination_n != NULL)
        {
            destination_n* destination_n_1 = NULL;

            if (DEBUG)
            {
                char addrString[MAX_STRING_LENGTH];

                IO_ConvertIpAddressToString(
                    &list_destination_n->destination->rt_dst,
                    addrString);

                printf("Node %d, Last hop %s\n",
                    node->nodeId,
                    addrString);
            }
			

			//SYMMETRIC TOPOLOGY TABLE

			//Peter comment: find from the topology table if there is some entry 
			//whose last hop equal the specific dest hop of 2 or more (* since every loop will
			// increase the one more hop count) hop neighbors
         	if (SYMMETRIC_TOPOLOGY_TABLE)
			{

				topo_last = OlsrLookupLastTopologyTableSYM(node, list_destination_n->destination->rt_dst);
			}
			else
			{

				topo_last = OlsrLookupLastTopologyTable(node, list_destination_n->destination->rt_dst);
			}

			if (NULL != topo_last)
            {

				topo_dest = topo_last->topology_list_of_destinations;

		

                while (topo_dest != NULL)
                {

					Address addrReached = topo_dest->destination_node->topology_destination_dst;

                    if (RoutingOlsrCheckMyIfaceAddress(
                            node,
                            topo_dest->destination_node->topology_destination_dst) != -1)
                    {
                        topo_dest = topo_dest->next;
                        continue;
                    }


					OlsrCalculateRoutingTableForSinglePathTopologySearchHelpFuncForCompare(node, addrReached, list_destination_n, &list_destination_n_1, &tmp_destination_tail);


				
                    topo_dest = topo_dest->next;
                }
            }

            destination_n_1 = list_destination_n;
            list_destination_n = list_destination_n->next;
            MEM_free(destination_n_1);
        }

        list_destination_n = list_destination_n_1;
		//ui_metric_cost_limitation++;
    }

  
	
	//Peter Need to check !!!!!!!!!!!!!
	//OlsrInsertRoutingTableFromHnaTable(node);



    //OlsrReleaseRoutingTable(olsr->mirror_table);

}



static
void OlsrCalculateRoutingTableAdv(Node *node)
{

	//Peter Adder for test time complexity

	//g_iTopologyChgApplyARC++;

	//if (node->nodeId == 1)
	{

		//printf("OlsrCalculateRoutingTableAdv Begin \n");
	}
	

	/*
	char strTxt[2048];
	memset(strTxt, 0, 2048 * sizeof(char));
	*/

	if (g_iTestRCSimAndRealTime == 1)
	{

		if (node->nodeId == DEBUG_NODE_ID)
		{
			char timeStr3[MAX_STRING_LENGTH];

			TIME_PrintClockInSecond(getSimTime(node), timeStr3, node);

			char timeStr4[MAX_STRING_LENGTH];

			TIME_PrintClockInSecond(EXTERNAL_QueryRealTime(), timeStr4, node);

			double ddSimTimeStart = atof(timeStr3);
			double ddRealTimeStart = atof(timeStr4);

			//printf("OlsrCalculateRoutingTableAdv start for node No.%d, ddSimTimeStart = %f, ddRealTimeStart = %f \n", 
			//	node->nodeId, ddSimTimeStart, ddRealTimeStart);
		}
	}


	tc_trace_item tti;

	if (_TEST_TIME_COMPLEXITY && g_iSimplifiedTimeTest == 0)
	{
		
		//if (node->nodeId == NODE_ID_FOR_TEST_OUTER_ANGLE || node->nodeId == NODE_ID_FOR_TEST_OUTER_EDGE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_ANGLE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_EDGE || node->nodeId == NODE_ID_FOR_TEST_CENTER)
		if (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END)
		{
			/*
			sprintf(strTxt, "%s\n", strTxt);

			sprintf(strTxt, "%sOlsrCalculateRoutingTableAdv Start ************************************************* \n", strTxt); 
			*/

			memset(&tti, 0, sizeof(tc_trace_item));
			tti.bIsAdvOrNot = true;
		}
	}

	
	
	//For execution time compute
	
	double dSimTimeStart = 0.0;
	double dRealTimeStart = 0.0;

	double dSimTimeEnd = 0.0;
	double dRealTimeEnd = 0.0;
	
	
	
	char timeStr[MAX_STRING_LENGTH];
	TIME_PrintClockInSecond(getSimTime(node), timeStr, node);

	BOOL bTimeConsumptionValidate = FALSE;

	int iSimTime = atoi(timeStr);
	
	dSimTimeStart = atof(timeStr);


    //if (_TEST_TIME_COMPLEXITY && (node->nodeId == NODE_ID_FOR_TEST_OUTER_ANGLE || node->nodeId == NODE_ID_FOR_TEST_OUTER_EDGE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_ANGLE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_EDGE || node->nodeId == NODE_ID_FOR_TEST_CENTER) && iSimTime > VALID_SIMULATE_CHECK_TIME)
	if (_TEST_TIME_COMPLEXITY && (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END) && iSimTime > VALID_SIMULATE_CHECK_TIME)
	{


		bTimeConsumptionValidate = TRUE;


		if (g_iSimplifiedTimeTest == 1)
		{
			char timeStr2[MAX_STRING_LENGTH];

			TIME_PrintClockInSecond(EXTERNAL_QueryRealTime(), timeStr2, node);

			
			dRealTimeStart = atof(timeStr2);
		}
		else
		{

			char timeStr[MAX_STRING_LENGTH];

			TIME_PrintClockInSecond(getSimTime(node), timeStr, node);

			char timeStr2[MAX_STRING_LENGTH];

			TIME_PrintClockInSecond(EXTERNAL_QueryRealTime(), timeStr2, node);

			dSimTimeStart = atof(timeStr);
			dRealTimeStart = atof(timeStr2);
			//int iSimTime = atoi(timeStr);

			//sprintf(strTxt, "%sOlsrCalculateRoutingTableAdv Start for node %d at time %f and %f: \n", strTxt, node->nodeId, dSimTimeStart, dRealTimeStart);

			tti.dCurrentSimTime = dSimTimeStart;
		}

		
    }
	
		
	//printf("!!!!!!!!!!!!!!    start OlsrCalculateRoutingTable \n");
	
	destination_n* list_destination_n = NULL;
    destination_n* list_destination_n_1 = NULL;
    topology_last_entry* topo_last;
    destination_list* topo_dest;

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

	if (olsr->changes_neighborhood)
	{
		g_iNeighborhoodChgApplyARC++;

		
	}
	else
	{
		g_iTopologyChgApplyARC++;
	}

    // RFC 3626 Section 10
    // Move routing table

	//ACCUMULATIVE_ROUTE_CALC == 1, modify the routing table directly,
	//so backup is not allowed which may cause current routing table become empty
	//OlsrRoutingMirror(node);
	   

    if (DEBUG)
    {
        printf(" Node %d : Printing Routing Table\n", node->nodeId);

        OlsrPrintRoutingTable(olsr->routingtable);

        printf(" Node %d : Printing Mirror Routing Table\n", node->nodeId);

        OlsrPrintRoutingTable(olsr->mirror_table);
    }

    // Step 1 Delete old entries from the table
    // empty previous routing table before creating a new one

    if (DEBUG)
    {
        printf("Empty IP forwarding table\n");
    }


	if (_TEST_TIME_COMPLEXITY)
	{
	}
	else
	{
		//ACCUMULATIVE_ROUTE_CALC == 1
		
		//NetworkEmptyForwardingTable(node, ROUTING_PROTOCOL_OLSR_INRIA);		
	}

    
    // Step 2 Add One hop neighbors
    if (DEBUG)
    {
        printf("Fill table with neighbors\n");
    }


	//ACCUMULATIVE_ROUTE_CALC == 1	
	// OlsrFillRoutingTableWithNeighbors(node);
	
 


    if (DEBUG)
    {
        printf("Fill table with two hop neighbors\n");
    }


	RoutingOlsr* olsrTmp = NULL;



	UInt32 uiLookupCntForAddList;
	
	UInt32 uiLookupCntFor2Hop;




	if (_TEST_TIME_COMPLEXITY && g_iSimplifiedTimeTest == 0)
	{
		uiLookupCntFor2Hop = 0;

		uiLookupCntForAddList = 0;
	}

    // Step 3 Add two hop neighbors
    
	//ACCUMULATIVE_ROUTE_CALC == 1
	/*
	//if (_TEST_TIME_COMPLEXITY && (node->nodeId == NODE_ID_FOR_TEST_OUTER_ANGLE || node->nodeId == NODE_ID_FOR_TEST_OUTER_EDGE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_ANGLE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_EDGE || node->nodeId == NODE_ID_FOR_TEST_CENTER))
	if (_TEST_TIME_COMPLEXITY && (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END))
	{

		list_destination_n_1 = OlsrFillRoutingTableWith2HopNeighbors(node, &uiLookupCntFor2Hop);
	}
	else
	{

		if (g_iAccumulativeRouteCalculation == 0)
		{

			list_destination_n_1 = OlsrFillRoutingTableWith2HopNeighbors(node);
		}
		else
		{
			
			

		}
		
	}
	*/
	
	//generate the specific work set for future use


	/*
	if (node->nodeId == 1 && getSimTime(node) > 5)
	{

	printf("Routing Table for node No. %d before custome delete from routing table, for uiConfidentCost %d \n", node->nodeId, olsr->uiConfidentCost);

	OlsrPrintRoutingTable(olsr->routingtable);
	}
	*/

	//if (node->nodeId == 16 && olsr->naRecentChangedAddressByTC == 15 && olsr->recent_delete_list != NULL && olsr->recent_add_list != NULL)
	{
		//DebugBreak();
	}

	//printf("OlsrCalculateRoutingTableAdv stage #1 \n");

	BOOL bAddDeleteSameTime = FALSE;
	if (olsr->recent_add_list != NULL && olsr->recent_delete_list != NULL)
	{
		bAddDeleteSameTime = TRUE;
	}

	destination_n* list_destination_delete = NULL;

	//g_iAccumulativeRouteCalculation should be != 0 for Adv option
	if (g_iAccumulativeRouteCalculation == 1)
	{

		if (olsr->recent_add_list != NULL)
		{
			if (olsr->changes_neighborhood)
			{

				if (_TEST_TIME_COMPLEXITY && g_iSimplifiedTimeTest == 0 && (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END))
				{
					list_destination_n_1 = ProcessRoutingTableAccordingToRecentAddListV44(node, &uiLookupCntForAddList);
				}
				else
				{
					list_destination_n_1 = ProcessRoutingTableAccordingToRecentAddListV44(node);
				}

			}
			else
			{
				if (_TEST_TIME_COMPLEXITY && g_iSimplifiedTimeTest == 0 && (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END))
				{
					//uiLookupCntForAddList = 0;

					list_destination_n_1  = ProcessRoutingTableAccordingToRecentAddListV2(node, &uiLookupCntForAddList);
				}
				else
				{
					list_destination_n_1  = ProcessRoutingTableAccordingToRecentAddListV2(node);
				}

			}
		}

		//list_destination_n_1 = ProcessRoutingTableAccordingToConfidentCost(node, olsr->uiConfidentCost);
	}
	else	//g_iAccumulativeRouteCalculation == 2
	{

		if (olsr->recent_add_list != NULL)
		{
			if (olsr->changes_neighborhood)
			{

				if (_TEST_TIME_COMPLEXITY && g_iSimplifiedTimeTest == 0 && (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END))
				{
					list_destination_n_1 = ProcessRoutingTableAccordingToRecentAddListV46(node, &list_destination_delete, &uiLookupCntForAddList);
				}
				else
				{
					list_destination_n_1 = ProcessRoutingTableAccordingToRecentAddListV46(node, &list_destination_delete);
				}

				
			}
			else
			{
				if (_TEST_TIME_COMPLEXITY && g_iSimplifiedTimeTest == 0 && (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END))
				{
					//uiLookupCntForAddList = 0;

					list_destination_n_1  = ProcessRoutingTableAccordingToRecentAddListV2(node, &uiLookupCntForAddList);
				}
				else
				{
					list_destination_n_1  = ProcessRoutingTableAccordingToRecentAddListV2(node);
				}

			}
		}
	}

	
	/*
	//if (node->nodeId == 1)
	{
		if (list_destination_n_1 == NULL)
		{
			printf("!!!!!!!!!!!!!!!!!!!!!!!!!!!!! list_destination_n_1 == NULL, uiConfidentCost = %d !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! \n", olsr->uiConfidentCost);

		}
		

	}
	*/


	/*
	if (node->nodeId == 1 && getSimTime(node) > 5)
	{

		printf("Routing Table for node No. %d after custome delete from routing table \n", node->nodeId);

		OlsrPrintRoutingTable(olsr->routingtable);
	}
	*/
	
	
	/*
	if (node->nodeId == 1)
	{
		printf("node 1 After OlsrFillRoutingTableWith2HopNeighbors: \n");


		olsrTmp = (RoutingOlsr* ) node->appData.olsr;
		OlsrPrintRoutingTable(olsrTmp->routingtable);

		OlsrPrintTopologyTable(node);
	}
	*/


	//Peter Adder for test time complexity
		
	UInt32 uiLookupCnt;
	
	if (_TEST_TIME_COMPLEXITY && g_iSimplifiedTimeTest == 0)
	{
		uiLookupCnt = 0;
	}



	// Peter Added for support _OLSR_MULTIPATH
	//UInt16 ui_metric_cost_limitation = 3;

	//if (g_iAccumulativeRouteCalculation == 1)
	{
		//ui_metric_cost_limitation = olsr->uiConfidentCost + 1;
	}

    // Step 3 Add the remaining destinations looking up the topology table
    list_destination_n = list_destination_n_1;

    while (list_destination_n_1 != NULL)
    {
        list_destination_n_1 = NULL;

		destination_n*  tmp_destination_tail = NULL;

        //Peter comment: every loop add group of destination nodes that one hop more from the source node,
		//compare to the group in the previous loop  
		while (list_destination_n != NULL)
        {
            destination_n* destination_n_1 = NULL;

            if (DEBUG)
            {
                char addrString[MAX_STRING_LENGTH];

                IO_ConvertIpAddressToString(
                    &list_destination_n->destination->rt_dst,
                    addrString);

                printf("Node %d, Last hop %s\n",
                    node->nodeId,
                    addrString);
            }
			
			//Peter comment: find from the topology table if there is some entry 
			//whose last hop equal the specific dest hop of 2 or more (* since every loop will
			// increase the one more hop count) hop neighbors
            if (SYMMETRIC_TOPOLOGY_TABLE)
			{
				topo_last = OlsrLookupLastTopologyTableSYM(node, list_destination_n->destination->rt_dst);
			}
			else
			{
				topo_last = OlsrLookupLastTopologyTable(node, list_destination_n->destination->rt_dst);
			}
			
			
			if (NULL != topo_last)
            {
                topo_dest = topo_last->topology_list_of_destinations;

			
                while (topo_dest != NULL)
                {
                 
					Address addrReached = topo_dest->destination_node->topology_destination_dst;

					if (RoutingOlsrCheckMyIfaceAddress(
						node,
						topo_dest->destination_node->topology_destination_dst) != -1)
					{
						topo_dest = topo_dest->next;
						continue;
					}


					OlsrCalculateRoutingTableForSinglePathTopologySearchHelpFunc(node, addrReached, list_destination_n, &list_destination_n_1, &tmp_destination_tail, TRUE);


					//Peter Added for test time complexity
					if (_TEST_TIME_COMPLEXITY && g_iSimplifiedTimeTest == 0)
					{

						//if (node->nodeId == NODE_ID_FOR_TEST_OUTER_ANGLE || node->nodeId == NODE_ID_FOR_TEST_OUTER_EDGE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_ANGLE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_EDGE || node->nodeId == NODE_ID_FOR_TEST_CENTER)
						if (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END)
						{
							uiLookupCnt++;

						}
					}

                    topo_dest = topo_dest->next;
                }
            }

            destination_n_1 = list_destination_n;
            list_destination_n = list_destination_n->next;
            MEM_free(destination_n_1);
        }

        list_destination_n = list_destination_n_1;
		//ui_metric_cost_limitation++;
    }


	/*
	if (olsr->recent_delete_list != NULL && olsr->recent_add_list != NULL)
	{

	}
	*/

	
	if (bAddDeleteSameTime)
	{
		if (g_iRunTimeCompare == 1)
		{
			
			CompareRTMiddle(node);		
		}
	}
	

	//printf("OlsrCalculateRoutingTableAdv stage #2 \n");


	UInt32 uiLookpCntForDelete = 0;

	if (g_iAccumulativeRouteCalculation == 1)
	{

		if (olsr->recent_delete_list != NULL)
		{

			
			UInt32 uiRequiredRediscovery = 0;
			BOOL bRequiredRediscovery = FALSE;			
			

			if (olsr->changes_neighborhood)
			{
				
				UInt32 uiDel43 = 0;
				//g_iTopologyChgApplyARC_With_Delete_Success++;

				if (olsr->bNeighborChgCausedRemoveFromHigherHop)
				{
					if (g_iSimplifiedTimeTest == 1)
					{
						ProcessRoutingTableAccordingToRecentDeleteListV44(node, &bRequiredRediscovery, NULL, NULL);
					}
					else
					{
						ProcessRoutingTableAccordingToRecentDeleteListV44(node, &bRequiredRediscovery, NULL, &uiDel43);
					}
					
				}
				else
				{						
					
					//printf("++++++++++++++++++++++ProcessRoutingTableAccordingToRecentDeleteListV43 called ! +++++++++++++++++++++++++\n");
					if (g_iSimplifiedTimeTest == 1)
					{
						ProcessRoutingTableAccordingToRecentDeleteListV43(node, &bRequiredRediscovery, NULL, NULL);
					}
					else
					{
						ProcessRoutingTableAccordingToRecentDeleteListV43(node, &bRequiredRediscovery, NULL, &uiDel43);
					}
					
					
				}


				/*
				while (list_destination_delete != NULL)
				{
					destination_n* destination_n_1 = NULL;

					destination_n_1 = list_destination_delete;
					list_destination_delete = (list_destination_delete)->next;


					if (destination_n_1 != NULL)
					{


						rt_entry* pdsttmp = NULL;

						pdsttmp = destination_n_1->destination;

						destination_n_1->destination = NULL;

						if (pdsttmp != NULL && pdsttmp->rt_metric == MAX_COST)
						{
							OlsrDeleteRoutingTable(pdsttmp);

							pdsttmp = NULL;
						}



						MEM_free(destination_n_1);
						destination_n_1 = NULL;

					}
				}
				*/

				uiLookpCntForDelete += uiDel43;

			}
			else
			{

				UInt32 uiDel33 = 0;
				
				//g_iTopologyChgApplyARC_With_Delete_Success++;
				ProcessRoutingTableAccordingToRecentDeleteListV33(node, NULL, NULL);
				
			}		
			
		}
		
		
	}
	else	//g_iAccumulativeRouteCalculation == 2
	{

		if (olsr->changes_neighborhood && olsr->bNeighborChgCausedRemoveFromHigherHop)
		{

			//clear_tco_node_addr_set(&olsr->recent_delete_list);

			//it is possible that olsr->recent_delete_list is NULL but list_destination_delete is not NULL
			//because of the InsideNode may cause this mismatch
			
			/*
			while (list_destination_delete != NULL)
			{
				destination_n* destination_n_1 = NULL;

				destination_n_1 = list_destination_delete;
				list_destination_delete = (list_destination_delete)->next;


				if (destination_n_1 != NULL)
				{


					rt_entry* pdsttmp = NULL;

					pdsttmp = destination_n_1->destination;

					destination_n_1->destination = NULL;

					if (pdsttmp != NULL && pdsttmp->rt_metric == MAX_COST)
					{
						OlsrDeleteRoutingTable(pdsttmp);

						pdsttmp = NULL;
					}
				


					MEM_free(destination_n_1);
					destination_n_1 = NULL;

				}
			}
			*/
		}

		

		if (olsr->recent_delete_list != NULL || olsr->changes_neighborhood && list_destination_delete != NULL)
		{

			//printf("OlsrCalculateRoutingTableAdv stage #2.1 \n");

			BOOL bRequiredRediscovery = FALSE;

			if (FALSE)
			//if (node->nodeId == 20 && olsr->naRecentChangedAddressByTC == 2)
			//if (node->nodeId == 75)
			{

				
				
				/*
				printf("olsr->naRecentChangedAddressByTC = %d \n",olsr->naRecentChangedAddressByTC);

				OlsrPrintNeighborTable(node);

				printf("\n");
				
				OlsrPrint2HopNeighborTable(node);

				printf("\n");

				*/
				/*
				OlsrPrintTopologyTable(node);

				printf("\n");


				OlsrPrintDestTopologyTable(node);

				
				printf("\n");
				*/

				//OlsrPrintTopologyTableSYM(node);


				//printf("\n");
				//if (olsr->recent_add_list != NULL)
				//if (FALSE)
				{
					//printf("===========================================================================\n\n");

					g_iChaseRouteTable = 0;
					OlsrPrintRoutingTable(olsr->routingtable);
					g_iChaseRouteTable = 1;

					//DebugBreak();

					//printf("*************************************************************************\n\n");
				}

				

				//printf("\n");




				//DebugBreak();
			}
			

			
			UInt32 uiRequiredRediscovery = 0;
			
			

			if (olsr->changes_neighborhood)
			{
				
				UInt32 uiDel43 = 0;
				//g_iTopologyChgApplyARC_With_Delete_Success++;

				if (olsr->bNeighborChgCausedRemoveFromHigherHop)
				{

					if (g_iSimplifiedTimeTest == 1)
					{
						ProcessRoutingTableAccordingToRecentDeleteListV44(node, &bRequiredRediscovery, &list_destination_delete, NULL);
					}
					else
					{
						ProcessRoutingTableAccordingToRecentDeleteListV44(node, &bRequiredRediscovery, &list_destination_delete, &uiDel43);
					}
					
					

					
				}
				else
				{	
					
					
					//printf("++++++++++++++++++++++ProcessRoutingTableAccordingToRecentDeleteListV43 called ! +++++++++++++++++++++++++\n");
					
					if (g_iSimplifiedTimeTest == 1)
					{
						ProcessRoutingTableAccordingToRecentDeleteListV43(node, &bRequiredRediscovery, &list_destination_delete, NULL);
					}
					else
					{
						ProcessRoutingTableAccordingToRecentDeleteListV43(node, &bRequiredRediscovery, &list_destination_delete, &uiDel43);
					}

					
				}


				while (list_destination_delete != NULL)
				{
					destination_n* destination_n_1 = NULL;

					destination_n_1 = list_destination_delete;
					list_destination_delete = (list_destination_delete)->next;


					if (destination_n_1 != NULL)
					{


						rt_entry* pdsttmp = NULL;

						pdsttmp = destination_n_1->destination;

						destination_n_1->destination = NULL;

						if (pdsttmp != NULL && pdsttmp->rt_metric == MAX_COST)
						{
							OlsrDeleteRoutingTable(pdsttmp);

							pdsttmp = NULL;
						}



						MEM_free(destination_n_1);
						destination_n_1 = NULL;

					}
				}

				uiLookpCntForDelete += uiDel43;

			}
			else
			{


				//list_destination_n_1  = ProcessRoutingTableAccordingToRecentDeleteListV2(node, &bRequiredRediscovery, &uiLookpCntForDelete);
				//list_destination_n_1  = ProcessRoutingTableAccordingToRecentDeleteListV3(node, &bRequiredRediscovery, &uiLookpCntForDelete);


				//list_destination_n_1  = ProcessRoutingTableAccordingToRecentDeleteListV20(node, &bRequiredRediscovery, &uiLookpCntForDelete);

				//list_destination_n_1  = ProcessRoutingTableAccordingToRecentDeleteListV21(node, &bRequiredRediscovery, &uiLookpCntForDelete);



				//list_destination_n_1  = ProcessRoutingTableAccordingToRecentDeleteListV21(node, &uiRequiredRediscovery, &uiLookpCntForDelete);
				
				
				if (g_iSimplifiedTimeTest == 1)
				{
					list_destination_n_1  = ProcessRoutingTableAccordingToRecentDeleteListV23(node, &uiRequiredRediscovery, NULL);
				}
				else
				{
					list_destination_n_1  = ProcessRoutingTableAccordingToRecentDeleteListV23(node, &uiRequiredRediscovery, &uiLookpCntForDelete);
				}

				



				g_iTopologyChgApplyARC_With_Delete++;

				//printf("OlsrCalculateRoutingTableAdv stage #2.2 \n");


				if (list_destination_n_1 != NULL)
				{
					//DebugBreak();

					if (g_iSimplifiedTimeTest == 1)
					{
						ProcessRoutingTableAccordingToRecentDeleteListV53(node, &olsr->recent_add_list, NULL, list_destination_n_1);
					}
					else
					{
						ProcessRoutingTableAccordingToRecentDeleteListV53(node, &olsr->recent_add_list, &uiLookpCntForDelete, list_destination_n_1);
					}

					

				}
				else
				{

					//printf("OlsrCalculateRoutingTableAdv stage #2.2.3 \n");

					/*
					if (uiRequiredRediscovery != 0)
					{

						//printf("OlsrCalculateRoutingTableAdv stage #2.2.3.1 \n");

						//OlsrCalculateRoutingTable(node, TRUE, &uiLookpCntForDelete);

						if (uiRequiredRediscovery == 2)
						{
							UInt32 uiDel33 = 0;
							g_iTopologyChgApplyARC_With_Delete_Success++;
							ProcessRoutingTableAccordingToRecentDeleteListV33(node, &bRequiredRediscovery, &uiDel33);


							uiLookpCntForDelete += uiDel33;
						}
						else	//1
						{
							g_iTopologyChgApplyARC_With_Delete_Failed_Cause_Rediscovery++;

							OlsrCalculateRoutingTable(node, TRUE, &uiLookpCntForDelete);
						}



					}
					else
					{
						g_iTopologyChgApplyARC_With_Delete_Success++;
						//do nothing here, since it is possible that there is no other node nearby the deleted node,
						//or every neighbor can find perfect nodes for replace.

						//printf("OlsrCalculateRoutingTableAdv stage #2.2.3.2 \n");
					}
					*/

					//already have done by OlsrCalculateRoutingTable version
					//printf("OlsrCalculateRoutingTableAdv stage #2.2.4 \n");
				}


				//printf("OlsrCalculateRoutingTableAdv stage #2.4 \n");
			}

			
			
		}
	}


	//printf("OlsrCalculateRoutingTableAdv stage #3 \n");

    if (DEBUG)
    {
        printf(" Node %d : Printing Routing Table\n", node->nodeId);
        OlsrPrintRoutingTable(olsr->routingtable);

        printf(" Node %d : Printing Mirror Routing Table\n", node->nodeId);
        OlsrPrintRoutingTable(olsr->mirror_table);
    }



	/*
	if (node->nodeId == 1 && getSimTime(node) > 5)
	{

		printf("Routing Table for node No. %d after Advanced routing table re-calculation \n", node->nodeId);

		OlsrPrintRoutingTable(olsr->routingtable);
	}
	*/
    

	//Peter Need to check !!!!!!!!!!!!!
	OlsrInsertRoutingTableFromHnaTable(node);


	if (g_iAccumulativeRouteCalculation == 0)
	{
		OlsrReleaseRoutingTable(olsr->mirror_table);
	}
   


	//printf("!!!!!!!!!!!!!!    end OlsrCalculateRoutingTable \n");
	
	

	//if (_TEST_TIME_COMPLEXITY && (node->nodeId == NODE_ID_FOR_TEST_OUTER_ANGLE || node->nodeId == NODE_ID_FOR_TEST_OUTER_EDGE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_ANGLE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_EDGE || node->nodeId == NODE_ID_FOR_TEST_CENTER) && bTimeConsumptionValidate)
	if (_TEST_TIME_COMPLEXITY && (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END) && bTimeConsumptionValidate)
	{

		if (g_iSimplifiedTimeTest == 1)
		{
			char timeStr2[MAX_STRING_LENGTH];

			TIME_PrintClockInSecond(EXTERNAL_QueryRealTime(), timeStr2, node);

			
			dRealTimeEnd = atof(timeStr2);

			double dDuration = dRealTimeEnd - dRealTimeStart;

			olsr->dRCRealRuntime += dDuration;


			if (dSimTimeStart < olsr->dRecentRCStartTime)
			{
				//printf("|||||||||||||||||=======================OlsrCalculateRoutingTableAdv Start Time Exception =======================|||||||||||||| dSimTimeStart = %f dRecentRCStartTime = %f \n", dSimTimeStart, olsr->dRecentRCStartTime);
				
				//this will never happen
			}


			double dExpectedEndTime = 0.0;

			if (dSimTimeStart > olsr->dRecentRCStartTime && dSimTimeStart < olsr->dRecentRCEndTime)
			{
				//printf("|||||||||||||||||=======================OlsrCalculateRoutingTable when computing RC TIME=======================|||||||||||||| dRecentRCStartTime = %f dRecentRCEndTime = %f CurrentSimTime = %f \n", olsr->dRecentRCStartTime, olsr->dRecentRCEndTime, dSimTimeStart);
				dExpectedEndTime = olsr->dRecentRCEndTime + dDuration;
			}
			else
			{
				olsr->dRecentRCStartTime = dSimTimeStart;
				dExpectedEndTime = dSimTimeStart + dDuration;
			}




			if (dExpectedEndTime > olsr->dRecentRCEndTime)
			{
				olsr->dRecentRCEndTime = dExpectedEndTime;
			}
			else
			{
				//printf("|||||||||||||||||=======================OlsrCalculateRoutingTableAdv End Time Exception =======================|||||||||||||| dExpectedEndTime = %f dRecentRCEndTime = %f \n", dExpectedEndTime, olsr->dRecentRCEndTime);

			}

			

			//olsr->dRecentRCEndTime = olsr->dRecentRCStartTime + dDuration;

			olsr->uiRCAdvCount++;
		}
		else
		{
			char timeStr[MAX_STRING_LENGTH];

			TIME_PrintClockInSecond(getSimTime(node), timeStr, node);

			char timeStr2[MAX_STRING_LENGTH];

			TIME_PrintClockInSecond(EXTERNAL_QueryRealTime(), timeStr2, node);

			dSimTimeEnd = atof(timeStr);
			dRealTimeEnd = atof(timeStr2);
			//int iSimTime = atoi(timeStr);

			/*
			sprintf(strTxt, "%sOlsrCalculateRoutingTableAdv End for node %d at time %f and %f: \n", strTxt, node->nodeId, dSimTimeEnd, dRealTimeEnd);


			sprintf(strTxt, "%sOlsrCalculateRoutingTableAdv Time consumption for node %d: real_time = %f \n", strTxt, node->nodeId, 
				dRealTimeEnd - dRealTimeStart);
			*/

			tti.dRealTimeDuration = dRealTimeEnd - dRealTimeStart;
		}
		
		

		//DebugBreak();
	}
	
	if (g_iTestRCSimAndRealTime == 1)
	{

		if (node->nodeId == DEBUG_NODE_ID)
		{
			char timeStr3[MAX_STRING_LENGTH];

			TIME_PrintClockInSecond(getSimTime(node), timeStr3, node);

			char timeStr4[MAX_STRING_LENGTH];

			TIME_PrintClockInSecond(EXTERNAL_QueryRealTime(), timeStr4, node);

			double ddSimTimeStart = atof(timeStr3);
			double ddRealTimeStart = atof(timeStr4);

			/*
			if (ddSimTimeStart > 21 && ddSimTimeStart < 23)
			{

				printf("OlsrCalculateRoutingTableAdv end for node No.%d, ddSimTimeStart = %f, ddRealTimeStart = %f \n", 
					node->nodeId, ddSimTimeStart, ddRealTimeStart);
				
				
				if (olsr->pszRTWithARC == NULL)
				{
					olsr->pszRTWithARC = new char[RT_SIZE];
				}
				
				memset(olsr->pszRTWithARC, 0, RT_SIZE * sizeof(char));
			

				OlsrPrintRoutingTable(olsr->routingtable, olsr->pszRTWithARC);

				printf(olsr->pszRTWithARC);
			}
			*/
		}
	}

	//Peter Adder for test time complexity
	
	if (_TEST_TIME_COMPLEXITY && g_iSimplifiedTimeTest == 0)
	{
		
		//if (node->nodeId == NODE_ID_FOR_TEST_OUTER_ANGLE || node->nodeId == NODE_ID_FOR_TEST_OUTER_EDGE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_ANGLE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_EDGE || node->nodeId == NODE_ID_FOR_TEST_CENTER)
		if (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END)
		{

			/*
			sprintf(strTxt, "%sOlsrCalculateRoutingTableAdv End : uiLookupCnt = %d, uiLookupCntFor2Hop = %d ******************************* \n", strTxt, uiLookupCnt, uiLookupCntFor2Hop); 
			sprintf(strTxt, "%sOlsrCalculateRoutingTableAdv Combiled Count for node %d: CombiledCnt = %d ******************************* \n\n", strTxt, node->nodeId, uiLookupCnt + uiLookupCntFor2Hop); 
			*/

			tti.iCombinedCnt = uiLookupCnt + uiLookupCntFor2Hop;

			if (g_iAccumulativeRouteCalculation == 1)
			{
			}
			else
			{

				tti.iCombinedCnt += uiLookpCntForDelete;
				
				tti.iCombinedCnt += uiLookupCntForAddList;

				/*
				if (uiLookupCntForAddList != 0)
				{
					DebugBreak();
				}
				*/
			}

			PUSH_BACK_CURRENT_ITEM(olsr, tti);

		}


		//sprintf(g_strTxt, "%s \n %s", g_strTxt, strTxt);

	
	}

	//printf("OlsrCalculateRoutingTableAdv End \n");

}


/***************************************************************************
 *                    Definition of general functions                      *
 ***************************************************************************/

// /**
// FUNCTION   :: OlsrProcessChanges
// LAYER      :: APPLICATION
// PURPOSE    :: This function processes for changes
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// RETURN :: void : NULL
// **/

static
Int32 OlsrProcessChanges(
    Node* node)
{
    RoutingOlsr* olsr = (RoutingOlsr *) node->appData.olsr;

	/*
	printf("OlsrProcessChanges called for node->nodeId = %d with changes_neighborhood = %d & changes_topology = %d \n", 
		node->nodeId, olsr->changes_neighborhood, olsr->changes_topology);
	*/

	/*
	char * pszInfo = NULL;
	char * pszOrigRT = NULL;
	char * pszMiddleRT = NULL;
	char * pszRTWithARC = NULL;
	char * pszRTWithoutARC = NULL;
	*/

    if (DEBUG)
    {
        if (olsr->changes_neighborhood)
        {
            printf("Changes in neighborhood\n");
        }
        if (olsr->changes_topology)
        {
            printf("Changes in topology\n");
        }
    }


	//Peter added for testing
	if (olsr->changes_neighborhood && olsr->changes_topology)
	{
	
		g_iBothChg++;
	}

	//Peter added to support route cache
	if (olsr->changes_neighborhood || olsr->changes_topology)
	{

		olsr->rci.bIsUseful = FALSE;
	}

    if (olsr->changes_neighborhood)
    {

		//Peter added for test
		g_iNeighborChangeCnt++;

        // Calculate new mprs and routing table
        OlsrCalculateMpr(node);

		if (_OLSR_MULTIPATH)
		{
			OlsrCalculateRoutingTableForMultiPath(node);
		}
		else
		{

			if (g_iAccumulativeRouteCalculation == 0)
			{

				OlsrCalculateRoutingTable(node);
			}
			else if (g_iAccumulativeRouteCalculation == 1)
			{


				if (olsr->recent_delete_list != NULL  || olsr->recent_add_list != NULL)
				{
					int iAddorDelete = 0;

					if (g_iRunTimeCompare == 1)
					{
						iAddorDelete = CmpBreakPoint(node);


						CompareRTPre(node);
					}

					//goes to the branch for g_iAccumulativeRouteCalculation == 1
					OlsrCalculateRoutingTableAdv(node);


					if (g_iRunTimeCompare == 1)
					{
						CompareRT(node, iAddorDelete);

					}
				}
				else
				{
					OlsrCalculateRoutingTable(node);
				}
								
			}
			else	//g_iAccumulativeRouteCalculation == 2
			{
				
				
				if (olsr->recent_delete_list != NULL  || olsr->recent_add_list != NULL)
				//if (FALSE)
				{

					//CmpBreakPoint(node);

					int iAddorDelete = 0;

					if (g_iRunTimeCompare == 1)
					{

						

						iAddorDelete = CmpBreakPoint(node);
						

						CompareRTPre(node);



					}

				
					
					if (olsr->recent_delete_list != NULL)
					{

						//CmpBreakPoint(node);

						if (g_iRunTimeCompare == 1)
						{

							//CompareRTPre(node);



						}
						//OlsrCalculateRoutingTableAdv(node);
						OlsrCalculateRoutingTableAdv(node);


						if (g_iRunTimeCompare == 1)
						{
							//CompareRT(node);

						}
					}
					else
					{
						if (exist_in_tco_node_addr_set(&olsr->recent_add_list, olsr->naRecentChangedAddressByTC))
						{
							//OlsrCalculateRoutingTable(node);

							if (olsr->bNeighborChgCausedRemoveFromHigherHop)
							{
								//OlsrCalculateRoutingTable(node);
								OlsrCalculateRoutingTableAdv(node);
							}
							else
							{
								int iCnt = 0;

								/*
								tco_node_addr * tco_tmp = olsr->recent_add_list;

								while (tco_tmp != NULL)
								{
									iCnt++;

									tco_tmp = tco_tmp->next;
								}
								*/

								if (iCnt > 1)
								{
									OlsrCalculateRoutingTableAdv(node);
								}
								else
								{
									OlsrCalculateRoutingTableAdv(node);
									//OlsrCalculateRoutingTableAdv(node);

								}

							}
							
						}
						else
						{
							OlsrCalculateRoutingTableAdv(node);
							//OlsrCalculateRoutingTable(node);
						}
					}
					
					if (g_iRunTimeCompare == 1)
					{
						CompareRT(node, iAddorDelete);

					}

					
					//OlsrCalculateRoutingTable(node);
				}
				else
				{
					OlsrCalculateRoutingTable(node);
				}
			}



			//OlsrCalculateRoutingTable(node);
		}
        
        		
		olsr->changes_neighborhood = FALSE;
        olsr->changes_topology = FALSE;



		//printf("After OlsrProcessChanges: \n");

		//OlsrPrintRoutingTable(olsr->routingtable);

        return 0;
    }

    if (olsr->changes_topology)
    {       	

		//Peter added for test
		g_iTopologyChangeCnt++;

		//DebugBreak();	
		// calculate the routing table
		if (_OLSR_MULTIPATH)
		{

			if (g_iAccumulativeRouteCalculation == 0)
			{

				OlsrCalculateRoutingTableForMultiPath(node);
			}
			else if (g_iAccumulativeRouteCalculation == 1)
			{

				/*
				
				*/

				/*
				if (olsr->uiConfidentCost >= 3)
				{

					OlsrCalculateRoutingTableForMultiPathAdv(node);
				}
				else
				{

					//can be more detailed for 1 and 2 cases,
					//but just skip currently 

					OlsrCalculateRoutingTableForMultiPath(node);
				}
				*/
			}
			else //g_iAccumulativeRouteCalculation == 2
			{
			
				if (olsr->recent_delete_list != NULL  || olsr->recent_add_list != NULL)
				{
					OlsrCalculateRoutingTableForMultiPathAdv(node);
				}
				else
				{
					OlsrCalculateRoutingTableForMultiPath(node);
				}
			}
			
		}
		else
		{

			if (g_iAccumulativeRouteCalculation == 0)
			{

				OlsrCalculateRoutingTable(node);
			}
			else if (g_iAccumulativeRouteCalculation == 1)
			{

				/*
				if (olsr->uiConfidentCost >= 3)
				{
	
					OlsrCalculateRoutingTableAdv(node);					
				}
				else
				{

					//can be more detailed for 1 and 2 cases,
					//but just skip currently 
					OlsrCalculateRoutingTable(node);
				}
				*/

				if (olsr->recent_delete_list != NULL  || olsr->recent_add_list != NULL)
				{

					int iAddorDelete = 0;

					if (g_iRunTimeCompare == 1)
					{
						iAddorDelete = CmpBreakPoint(node);


						CompareRTPre(node);
					}

					//goes to the branch for g_iAccumulativeRouteCalculation == 1
					OlsrCalculateRoutingTableAdv(node);

					if (g_iRunTimeCompare == 1)
					{
						CompareRT(node, iAddorDelete);
					}
				}
				else
				{
					OlsrCalculateRoutingTable(node);
				}

			}
			else	//g_iAccumulativeRouteCalculation == 2
			{
				/*
				if (olsr->recent_delete_list != NULL)
				{
					//OlsrCalculateRoutingTable(node);
				}
				else
				{
					//OlsrCalculateRoutingTableAdv(node);	
				}
				*/



				if (olsr->recent_delete_list != NULL  || olsr->recent_add_list != NULL)
				//if (FALSE)
				{
					//OlsrCalculateRoutingTableAdv(node);
					int iAddorDelete = 0;

					//CmpBreakPoint(node);
					if (g_iRunTimeCompare == 1)
					{
						iAddorDelete = CmpBreakPoint(node);
						CompareRTPre(node);



					}
					else
					{
						//CmpBreakPoint(node);
					}
					
					
					if (olsr->recent_delete_list != NULL && olsr->recent_add_list == NULL)
					{

						//OlsrCalculateRoutingTable(node);
						OlsrCalculateRoutingTableAdv(node);
					}
					else
					{
						//OlsrCalculateRoutingTable(node);
						OlsrCalculateRoutingTableAdv(node);
					}					
				

					if (g_iRunTimeCompare == 1)
					{
						CompareRT(node, iAddorDelete);
					}

					

					


				}
				else
				{
					OlsrCalculateRoutingTable(node);
				}
			}
			
		}


		//printf("After OlsrProcessChanges: \n");

		//OlsrPrintRoutingTable(olsr->routingtable);


        olsr->changes_topology = FALSE;
    }

    return 0;
}


// /**
// FUNCTION   :: OlsrDeleteTimeoutEntries
// LAYER      :: APPLICATION
// PURPOSE    :: This function removes all tuples for all tables when timer
//               is expired
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// RETURN :: void : NULL
// **/

static
void OlsrDeleteTimeoutEntries(
    Node* node)
{
    if (DEBUG)
    {
        printf("hold timer expired for node %d\n", node->nodeId);
    }

    OlsrTimeoutDuplicateTable(node);
    OlsrTimeoutMprSelectorTable(node);
    OlsrTimeoutNeighborhoodTables(node);
    OlsrTimeoutTopologyTable(node);
    OlsrTimeoutLinkEntry(node);

    OlsrProcessChanges(node);
}

// /**
// FUNCTION   :: OlsrReleaseTables
// LAYER      :: APPLICATION
// PURPOSE    :: This function releases all entries for all tables
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// RETURN :: void : NULL
// **/

static
void OlsrReleaseTables(
    Node* node)
{
    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    OlsrReleaseDuplicateTable(node);
    OlsrReleaseMprSelectorTable(node);
    OlsrReleaseNeighborTable(node);

    OlsrReleaseRoutingTable(olsr->mirror_table);
    OlsrReleaseRoutingTable(olsr->routingtable);

    OlsrReleaseTopologyTable(node);
	
	//Peter added for combine...
	OlsrReleaseCombinedTopologyTable(node);
    
	OlsrRelease2HopNeighborTable(node);
}

// /**
// FUNCTION   :: OlsrInitTables
// LAYER      :: APPLICATION
// PURPOSE    :: This function initialzes all the tables
// PARAMETERS ::
// + olsr : RoutingOlsr* : Pointer to olsr data structure
// RETURN :: void : NULL
// **/

static
void OlsrInitTables(RoutingOlsr *olsr)
{
    unsigned char index;


	//Peter added for support Angle sector
	olsr->dSectorDegree = 0.0;
	

	if (g_iSimplifiedTimeTest == 0)
	{

		olsr->pvt_TTIs = new tc_trace_item[TC_DEFAULT_SIZE];
		olsr->iTcItemSize = TC_DEFAULT_SIZE;

		memset(olsr->pvt_TTIs, 0, olsr->iTcItemSize * sizeof(tc_trace_item));
		olsr->iTcItemCnt = 0;
	}
	else
	{
		olsr->pvt_TTIs = NULL;
	}

	
	

	//Peter added for supporting accumulative route calculation
	olsr->naRecentChangedAddressByTC = 0;
	olsr->bNeighborChgCausedRemoveFromHigherHop = FALSE;
	//olsr->bUpdateOldOrAddNew = FALSE;
	olsr->bDeleteOld = FALSE;
	olsr->bAddNew = FALSE;

	olsr->recent_add_list = NULL;
	olsr->recent_delete_list = NULL;

	
	olsr->uiConfidentCost = 0;


    // Setting Link set to NULL
    olsr->link_set = NULL;

    olsr->neighbortable.neighborhash= (neighborhash_type*)
            MEM_malloc(HASHSIZE * sizeof(neighborhash_type));

    memset(olsr->neighbortable.neighborhash,
            0,
            HASHSIZE * sizeof(neighborhash_type));

    olsr->mprstable.mpr_selector_hash= (mpr_selector_hash_type*)
            MEM_malloc(HASHSIZE * sizeof(mpr_selector_hash_type));

    memset(
        olsr->mprstable.mpr_selector_hash,
        0,
        HASHSIZE * sizeof(mpr_selector_hash_type));

    olsr->midtable.mid_main_hash = (mid_main_hash_type*)
        MEM_malloc(HASHSIZE * sizeof(mid_main_hash_type));

    memset(olsr->midtable.mid_main_hash,
            0,
            HASHSIZE * sizeof(mid_main_hash_type));

    olsr->midtable.mid_alias_hash = (mid_alias_hash_type*)
        MEM_malloc(HASHSIZE * sizeof(mid_alias_hash_type));

    memset(olsr->midtable.mid_alias_hash,
            0,
            HASHSIZE * sizeof(mid_alias_hash_type));

	
    for (index = 0; index < HASHSIZE; index++)
    {
        olsr->neighbortable.neighborhash[index].neighbor_forw =
            (neighbor_entry *) &olsr->neighbortable.neighborhash[index];

        olsr->neighbortable.neighborhash[index].neighbor_back =
            (neighbor_entry *) &olsr->neighbortable.neighborhash[index];

        olsr->neighbortable.neighbor_mpr_seq = 0;

        olsr->neighbor2table[index].neighbor2_forw =
            (neighbor_2_entry *) &olsr->neighbor2table[index];

        olsr->neighbor2table[index].neighbor2_back =
            (neighbor_2_entry *) &olsr->neighbor2table[index];

        olsr->duplicatetable[index].duplicate_forw =
            (duplicate_entry *)&olsr->duplicatetable[index];

        olsr->duplicatetable[index].duplicate_back =
            (duplicate_entry *)&olsr->duplicatetable[index];

        olsr->mprstable.mpr_selector_hash[index].mpr_selector_forw =
            (mpr_selector_entry *) &olsr->mprstable.mpr_selector_hash[index];

        olsr->mprstable.mpr_selector_hash[index].mpr_selector_back =
            (mpr_selector_entry *) &olsr->mprstable.mpr_selector_hash[index];

        olsr->mprstable.ansn = 0;

        olsr->routingtable[index].rt_forw =
            (rt_entry *) &olsr->routingtable[index];

        olsr->routingtable[index].rt_back =
            (rt_entry *) &olsr->routingtable[index];

        olsr->mirror_table[index].rt_forw =
            (rt_entry *) &olsr->mirror_table[index];

        olsr->mirror_table[index].rt_back =
            (rt_entry *) &olsr->mirror_table[index];

        olsr->topologytable[index].topology_destination_forw =
            (topology_destination_entry *) &olsr->topologytable[index];

		olsr->topologytable[index].topology_destination_back =
            (topology_destination_entry *) &olsr->topologytable[index];


		//Peter Added for combine...
		olsr->combined_topologytable[index].topology_destination_forw =
			(topology_destination_entry *) &olsr->combined_topologytable[index];

		olsr->combined_topologytable[index].topology_destination_back =
			(topology_destination_entry *) &olsr->combined_topologytable[index];





		if (SYMMETRIC_TOPOLOGY_TABLE)
		{
			olsr->sym_topologylasttable[index].topology_last_forw =
				(topology_last_entry *) &olsr->sym_topologylasttable[index];

			olsr->sym_topologylasttable[index].topology_last_back =
				(topology_last_entry *) &olsr->sym_topologylasttable[index];

		}

		

        olsr->topologylasttable[index].topology_last_forw =
            (topology_last_entry *) &olsr->topologylasttable[index];

        olsr->topologylasttable[index].topology_last_back =
            (topology_last_entry *) &olsr->topologylasttable[index];

        olsr->midtable.mid_main_hash[index].mid_forw =
            (mid_entry *)&olsr->midtable.mid_main_hash[index];
        olsr->midtable.mid_alias_hash[index].mid_forw =
            (mid_address *)&olsr->midtable.mid_alias_hash[index];

        olsr->midtable.mid_main_hash[index].mid_back =
            (mid_entry *)&olsr->midtable.mid_main_hash[index];
        olsr->midtable.mid_alias_hash[index].mid_back =
            (mid_address *)&olsr->midtable.mid_alias_hash[index];

        olsr->hna_table[index].next =
            (hna_entry *) &olsr->hna_table[index];

        olsr->hna_table[index].prev =
            (hna_entry *) &olsr->hna_table[index];

    }
}


// /**
// FUNCTION   :: RoutingOlsrCheckMyIfaceAddress
// LAYER      :: APPLICATION
// PURPOSE    :: Function checks if address is not one of the
//               current node's interface address
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + addr : Address: Address to be checked
// RETURN :: Int32 : Returns interface index if match, else -1
// **/

Int32 RoutingOlsrCheckMyIfaceAddress(
    Node* node,
    Address addr)
{
    unsigned char index;
    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;
    Address interfaceAddress;

    for (index = 0; index < node->numberInterfaces; index++)
    {
        if (NetworkIpGetInterfaceType(node, index) != olsr->ip_version
            && NetworkIpGetInterfaceType(node, index)!= NETWORK_DUAL)
        {
            continue;
        }

        if(olsr->ip_version == NETWORK_IPV6)
        {
            interfaceAddress.networkType = NETWORK_IPV6;
            Ipv6GetGlobalAggrAddress(
                    node,
                    index,
                    &interfaceAddress.interfaceAddr.ipv6);
        }
        else if (olsr->ip_version == NETWORK_IPV4)
        {
            interfaceAddress.networkType = NETWORK_IPV4;
            interfaceAddress.interfaceAddr.ipv4 =
                            NetworkIpGetInterfaceAddress(node,index);
        }
//#endif

        if (Address_IsSameAddress(&interfaceAddress, &addr))
        {
            return index;
        }
    }

    return -1;
}


// /**
// FUNCTION   :: OlsrProcessNeighborsInHelloMsg
// LAYER      :: APPLICATION
// PURPOSE    :: This function process neighbors in hello msg
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + neighbor: neighbor_entry* : Pointer to neighbor entry
// + message : hl_message* : hello message pointer
// RETURN :: void : NULL
// **/

static
void OlsrProcessNeighborsInHelloMsg(
    Node* node,
    neighbor_entry* neighbor,
    hl_message* message)
{
    Address neigh_addr;
    hello_neighbor* message_neighbors;
    neighbor_2_list_entry* two_hop_neighbor_yet;
    neighbor_2_entry* two_hop_neighbor;

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    ERROR_Assert(neighbor, "Invalid neighbor entry");
    ERROR_Assert(message, "Invalid Hello message");

    message_neighbors = message->neighbors;

    while (message_neighbors != NULL)
    {
        if (RoutingOlsrCheckMyIfaceAddress(node, message_neighbors->address)
                                                                       == -1)
        {
            neigh_addr = OlsrMidLookupMainAddr(node,
                message_neighbors->address);

            if (!Address_IsAnyAddress(&neigh_addr))
            {
                message_neighbors->address = neigh_addr;
            }

            if ((message_neighbors->status == SYM_NEIGH)
                || (message_neighbors->status == MPR_NEIGH))
            {
                if ((two_hop_neighbor_yet =
                    OlsrLookupMyNeighbors(neighbor,
                        message_neighbors->address)) != NULL)
                {
                    // Updating the holding time for this neighbor
                    two_hop_neighbor_yet->neighbor_2_timer =
                            getSimTime(node)
                            + (clocktype)(message->vtime * SECOND);

                    two_hop_neighbor = two_hop_neighbor_yet->neighbor_2;

                    if (DEBUG)
                    {
                        char addrString[MAX_STRING_LENGTH];
                        IO_ConvertIpAddressToString(
                            &message_neighbors->address,
                            addrString);

                        printf("%s > Update second hop neighbor time\n",
                                addrString);
                    }
                }
                else
                {
                    if (DEBUG)
                    {
                        char addrString[MAX_STRING_LENGTH];
                        IO_ConvertIpAddressToString(
                            &message_neighbors->address,
                            addrString);

                        printf("%s > A new second hop neighbor\n",
                                addrString);
                    }

                    // Looking if the node is already in two hop neigh table
                    if ((two_hop_neighbor =
                        OlsrLookup2HopNeighborTable(
                            node, message_neighbors->address)) == NULL)
                    {
                        if(DEBUG)
                        {
                          printf("Adding entry in two hop neighbor table\n");
                        }

						{
							g_iNeighborChgByOlsrProcessNeighborsInHelloMsg++;

							g_iTopologyChgByOlsrProcessNeighborsInHelloMsg++;

						}
                        
						//Peter Comment: may need to deal with ###$$$%%%
						// the add of new 2hop neighbor may cause the cost of the descendants of this 2hop reduce.
						if (SYMMETRIC_TOPOLOGY_TABLE)
						{

							insert_into_tco_node_addr_set(&olsr->recent_add_list, message_neighbors->address.interfaceAddr.ipv4);
						}

						
						olsr->changes_neighborhood = TRUE;
                        olsr->changes_topology = TRUE;
                        two_hop_neighbor = (neighbor_2_entry *)
                            MEM_malloc(sizeof(neighbor_2_entry));

                        memset(
                            two_hop_neighbor,
                            0,
                            sizeof(neighbor_2_entry));

                        two_hop_neighbor->neighbor_2_nblist = NULL;
                        two_hop_neighbor->neighbor_2_pointer = 0;

                        two_hop_neighbor->neighbor_2_addr =
                            message_neighbors->address;

                        OlsrInsert2HopNeighborTable(
                            node,
                            two_hop_neighbor);

                        OlsrLinkingThis2Entries(
                            node,
                            neighbor,
                            two_hop_neighbor,
                            (float)message->vtime);
                    }
                    else
                    {
	                                        {
							g_iNeighborChgByOlsrProcessNeighborsInHelloMsg++;

							g_iTopologyChgByOlsrProcessNeighborsInHelloMsg++;

						}
                        
						//Peter Comment: may need to deal with ###$$$%%% 
						// may not deal with it, since only add a new 1st neighbor link to already exist 2hop neighbor will not change cost

						olsr->changes_neighborhood = TRUE;
                        olsr->changes_topology = TRUE;

                        // linking to this two_hop_neighbor entry
                        OlsrLinkingThis2Entries(
                            node,
                            neighbor,
                            two_hop_neighbor,
                            (float)message->vtime);
                    }
                }
            }
        }
        message_neighbors = message_neighbors->next;
    }
}

// /**
// FUNCTION   :: OlsrPrintTables
// LAYER      :: APPLICATION
// PURPOSE    :: Prints all the tables
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// RETURN :: void : NULL
// **/

static
void OlsrPrintTables(
    Node* node)
{
    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    printf("********************************* Node %d ********************"
            "**************\n", node->nodeId);


	// Peter comment: add for debuging
	/*
	if (node->nodeId != 1)
	{
		return;
		//DebugBreak();
	}
	*/

	//DebugBreak();
    
	
	// OlsrPrintDuplicateTable(node);
    OlsrPrintNeighborTable(node);
    OlsrPrintMprSelectorTable(node);
    //Peter Modified
    OlsrPrint2HopNeighborTable(node);
    
	if (SYMMETRIC_TOPOLOGY_TABLE)
	{
		/*
		if (node->nodeId == 1)
		{

			printf("g_iTopologyTableUpdateCount = %d !!!!!!!!!!!!!!!!!!!!! \n");
		}
		*/

		OlsrPrintTopologyTableSYM(node);
	}
	else
	{
		OlsrPrintTopologyTable(node);
	}

	//OlsrPrintTopologyTable(node);

	OlsrPrintDestTopologyTable(node);
	//OlsrPrintCombinedTopologyTable(node);
	

    // print MID table
    OlsrPrintMidTable(node);
    OlsrPrintHnaTable(node);

    OlsrPrintRoutingTable(olsr->routingtable);
}


// /**
// FUNCTION   :: OlsrCheckPacketSizeGreaterThanFragUnit
// LAYER      :: APPLICATION
// PURPOSE    :: Check weather the olsr packet size be greater than
// the allowed size.
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + msg : olsrpacket* : Pointer to Olsr Packet
// + h_ipv6_addr : in6_addr* : Pointer to ipv6 address
// RETURN :: void : NULL
// **/
static
void OlsrCheckPacketSizeGreaterThanFragUnit(Node* node,
                                            olsrpacket* msg,
                                            in6_addr* ipv6_addr)
{
    Int32 outputsize;
    Int32 allowedSize;

    char errStr[MAX_STRING_LENGTH];

    outputsize = (Int32)(((char *)ipv6_addr - (char *)msg) +
                                                           sizeof(in6_addr));

    allowedSize = GetNetworkIPFragUnit(node) - sizeof(ip6_hdr);

    if ( outputsize > MAXPACKETSIZE)
    {
        sprintf(errStr, "Packet size increases from the defined"
                        " MAXPACKETSIZE %d. \n",MAXPACKETSIZE);
        ERROR_Assert(FALSE,errStr);
    }
    else if (outputsize > (allowedSize))
    {
        sprintf(errStr, "Packet size above %d"
                        " is currently not supported.\n",allowedSize);
        ERROR_Assert(FALSE,errStr);
    }
}


// /**
// FUNCTION   :: OlsrCheckPacketSizeGreaterThanFragUnit
// LAYER      :: APPLICATION
// PURPOSE    :: Check weather the olsr packet size be greater than
// the allowed size.
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + msg : olsrpacket* : Pointer to Olsr Packet
// + h_ipv4_addr : NodeAddress* : Pointer to ipv4 address
// RETURN :: void : NULL
// **/
static
void OlsrCheckPacketSizeGreaterThanFragUnit(Node* node,
                                            olsrpacket* msg,
                                            NodeAddress* ipv4_addr)
{
    Int32 outputsize;
    Int32 allowedSize;

    char errStr[MAX_STRING_LENGTH];

    outputsize = (Int32)(((char *)ipv4_addr - (char *)msg) +
                                                        sizeof(NodeAddress));

    allowedSize = GetNetworkIPFragUnit(node) - sizeof(IpHeaderType);

    if ( outputsize > MAXPACKETSIZE)
    {
        sprintf(errStr, "Packet size increases from the defined"
                        " MAXPACKETSIZE %d. \n",MAXPACKETSIZE);
        ERROR_Assert(FALSE,errStr);
    }
    else if (outputsize > (allowedSize))
    {
        sprintf(errStr, "Packet size above %d"
                        " is currently not supported.\n",allowedSize);
        ERROR_Assert(FALSE,errStr);
    }
}


// /**
// FUNCTION   :: OlsrSendHello
// LAYER      :: APPLICATION
// PURPOSE    :: Generate HELLO packet with the contents of the parameter
//              "message". Can generate an empty HELLO packet if the
//              neighbor table is empty.
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + message : hl_message* : hello message to be inserted in packet
// + interfaceIndex : Int32 : Interface on which packet is to be transmitted
// RETURN :: void : NULL
// **/

static
void OlsrSendHello(
    Node* node,
    hl_message *message,
    Int32 interfaceIndex)
{
    // TBD: In cases where message size > max packet size
    // divide the packet and send it in parts..
    // Skipping this for now

    char packet [MAXPACKETSIZE + 1];
    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;
    Address main_address = olsr->main_address;

    olsrpacket* msg = (olsrpacket *)packet;
    olsrmsg* m = (olsrmsg *) msg->olsr_msg;

    hellomsg* h;
    hellinfo* hinfo;

    NodeAddress* h_ipv4_addr = NULL;
    in6_addr* h_ipv6_addr = NULL;

    hello_neighbor* nb;
    hello_neighbor* prev_nb;
    bool first_entry;
    Int32 outputsize;
    Int32 i;
    Int32 j;


    if (olsr->ip_version == NETWORK_IPV6)
    {
        h = m->olsr_ipv6_hello;
        hinfo = h->hell_info;
        h_ipv6_addr = (in6_addr *)hinfo->neigh_addr;
        outputsize = (Int32)((char *)h_ipv6_addr - (char *)packet);
        hinfo->link_msg_size = (UInt16) ((char *)h_ipv6_addr
                                   - (char *)hinfo);
        m->originator_ipv6_address = GetIPv6Address(main_address);
        m->olsr_msg_tail.olsr_ipv6_msg.ttl = message->ttl;
        m->olsr_msg_tail.olsr_ipv6_msg.hop_count = 0;
        m->olsr_msg_tail.olsr_ipv6_msg.msg_seq_no = OlsrGetMsgSeqNo(node);
    }
    else

    {
        h = m->olsr_ipv4_hello;
        hinfo = h->hell_info;
        h_ipv4_addr = (NodeAddress *)hinfo->neigh_addr;
        outputsize = (Int32)((char *)h_ipv4_addr - (char *)packet);
        hinfo->link_msg_size = (UInt16) ((char *)h_ipv4_addr
                                   - (char *)hinfo);
        m->originator_ipv4_address = GetIPv4Address(main_address);
        m->olsr_msg_tail.olsr_ipv4_msg.ttl = message->ttl;
        m->olsr_msg_tail.olsr_ipv4_msg.hop_count = 0;
        m->olsr_msg_tail.olsr_ipv4_msg.msg_seq_no = OlsrGetMsgSeqNo(node);
    }
    if (!message)
    {
        if (DEBUG)
        {
            printf("OlsrSendHello: NULL msg return.\n");
        }
        return;
    }

    if (DEBUG)
    {
        char addrString[MAX_STRING_LENGTH];
        IO_ConvertIpAddressToString(&main_address,
                addrString);

        char strTime[MAX_STRING_LENGTH];
        ctoa(getSimTime(node), strTime);
        printf("Node %d generates HELLO message with originator %s"
            " on interface %d at %s\n",
            node->nodeId, addrString, interfaceIndex, strTime);

        OlsrPrintHelloMessage(message);
    }
    olsr->olsrStat.numHelloSent++;

    m->olsr_msgtype = HELLO_PACKET;

    // For hello packet vtime is set to olsr->neighb_hold_time
    m->olsr_vtime = OlsrDouble2ME((Float32)(olsr->neighb_hold_time
                                                / SECOND));
    h->willingness = message->willingness;

    // Set htime to HELLO INTERVAL
    h->htime = OlsrDouble2ME((Float32)(olsr->hello_interval / SECOND));
    memset(&h->reserved, 0, sizeof(UInt16));

    for (i = 0; i <= MAX_NEIGH; i++)
    {
        for( j=0; j <= MAX_LINK;j++)
        {
            first_entry = true;
            for (nb = message->neighbors; nb != NULL; nb = nb->next)
            {

                if ((nb->status != i)||(nb->link != j))
                {
                    continue;
                }
                if (first_entry)
                {
                    memset(&hinfo->res, 0, sizeof(unsigned char));
                    hinfo->link_code = (unsigned char)CREATE_LINK_CODE(i,j);
                }

                if (olsr->ip_version == NETWORK_IPV6)
                {
                    //checking packet size
                    OlsrCheckPacketSizeGreaterThanFragUnit(node, msg,
                                                           h_ipv6_addr);

                    *h_ipv6_addr = GetIPv6Address(nb->address);
                    h_ipv6_addr++;
                }
                else

                {
                    //checking packet size
                    OlsrCheckPacketSizeGreaterThanFragUnit(node, msg,
                                                           h_ipv4_addr);

                    *h_ipv4_addr = GetIPv4Address(nb->address);
                    h_ipv4_addr++;
                }
                first_entry = false;
            }

            if (!first_entry)
            {

                if (olsr->ip_version == NETWORK_IPV6)
                {
                    hinfo->link_msg_size = (UInt16) ((char *)h_ipv6_addr
                                               - (char *)hinfo);
                    if (DEBUG)
                    {
                            printf(" Link message size is %d\n",
                                hinfo->link_msg_size);
                    }
                    hinfo = (hellinfo *)((char *)h_ipv6_addr);
                    h_ipv6_addr = (in6_addr *)hinfo->neigh_addr;
                }
                else

                {
                    hinfo->link_msg_size = (UInt16) ((char *)h_ipv4_addr
                                               - (char *)hinfo);
                    if (DEBUG)
                    {
                            printf(" Link message size is %d\n",
                                hinfo->link_msg_size);
                    }

                    hinfo = (hellinfo *)((char *)h_ipv4_addr);
                    h_ipv4_addr = (NodeAddress *)hinfo->neigh_addr;
                }

            }
        } // for j
    } // for i


   m->olsr_msg_size = (UInt16) ((char *)hinfo - (char *)m);

   if (DEBUG)
   {
       printf (" Node %d: Hello Message size is %d\n",
           node->nodeId, m->olsr_msg_size);
   }

   outputsize = (Int32)((char *)hinfo - (char *)packet);

   if (DEBUG)
   {
       printf (" Node %d: Hello Packet  size is %d\n",
           node->nodeId, outputsize);
   }

    msg->olsr_packlen = (UInt16) (outputsize);

    // Delete the list of neighbor messages
    nb = message->neighbors;

    while (nb)
    {
        prev_nb = nb;
        nb = nb->next;
        MEM_free(prev_nb);
    }

    OlsrSend(node, msg, outputsize, MAX_HELLO_JITTER, interfaceIndex);
}

// /**
// FUNCTION   :: OlsrSendTc
// LAYER      :: APPLICATION
// PURPOSE    :: Generate TC packet with the contents of the parameter
//              "message".
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + message : tc_message* : pointer to message which is to be inserted
//                           in packet
// + interfaceIndex : Int32 : interface to send the packet on
// RETURN :: void : NULL
// **/

static
void OlsrSendTc(Node *node, tc_message *message, Int32 interfaceIndex)
{
    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;
    char packet [MAXPACKETSIZE + 1];
    olsrpacket* msg = (olsrpacket *)packet;
    olsrmsg* m = msg->olsr_msg;
    tcmsg* tc = NULL;
    NodeAddress* mprs_ipv4_addr = NULL;
    in6_addr* mprs_ipv6_addr = NULL;

    tc_mpr_addr* mprs;
    tc_mpr_addr* prev_mprs;
    Int32 outputsize;

    if (olsr->ip_version == NETWORK_IPV6)
    {
        tc = m->olsr_ipv6_tc;
        mprs_ipv6_addr = (in6_addr *)tc->adv_neighbor_main_address;
    }
    else

    {
        tc = m->olsr_ipv4_tc;
        mprs_ipv4_addr = (NodeAddress *)tc->adv_neighbor_main_address;
    }

    if (!message)
    {
        if (DEBUG)
        {
            printf("OlsrSendTc: NULL msg return\n");
        }
        return;
    }

    olsr->olsrStat.numTcGenerated++;

    if (DEBUG)
    {
        char addrString[MAX_STRING_LENGTH];
        IO_ConvertIpAddressToString(&message->originator,
                addrString);

        char strTime[MAX_STRING_LENGTH];
        ctoa(getSimTime(node), strTime);
        printf("Node %d generates TC message with originator %s"
            " on interface %d at %s\n",
            node->nodeId, addrString, interfaceIndex, strTime);

        OlsrPrintTcMessage(message);
    }

    for (mprs = message->multipoint_relay_selector_address;
        mprs != NULL; mprs = mprs->next)
    {

        if (olsr->ip_version == NETWORK_IPV6)
        {
            //checking packet size
            OlsrCheckPacketSizeGreaterThanFragUnit(node, msg,
                                                           mprs_ipv6_addr);
            *mprs_ipv6_addr = GetIPv6Address(mprs->address);
            mprs_ipv6_addr++;
        }
        else

        {
            //checking packet size
            OlsrCheckPacketSizeGreaterThanFragUnit(node, msg,
                                                           mprs_ipv4_addr);
            *mprs_ipv4_addr = GetIPv4Address(mprs->address);
            mprs_ipv4_addr++;
        }
    }

    if (olsr->ip_version == NETWORK_IPV6)
    {
        outputsize = (Int32)((char *)mprs_ipv6_addr - packet);
        m->olsr_msg_size = (UInt16) ((char *)mprs_ipv6_addr - (char *)m);
        m->originator_ipv6_address = GetIPv6Address(message->originator);

        m->olsr_msg_tail.olsr_ipv6_msg.msg_seq_no = OlsrGetMsgSeqNo(node);
        m->olsr_msg_tail.olsr_ipv6_msg.hop_count = message->hop_count;
        m->olsr_msg_tail.olsr_ipv6_msg.ttl = message->ttl;
    }
    else

    {
        outputsize = (Int32)((char *)mprs_ipv4_addr - packet);
        m->olsr_msg_size = (UInt16) ((char *)mprs_ipv4_addr - (char *)m);
        m->originator_ipv4_address = GetIPv4Address(message->originator);
        m->olsr_msg_tail.olsr_ipv4_msg.msg_seq_no = OlsrGetMsgSeqNo(node);
        m->olsr_msg_tail.olsr_ipv4_msg.hop_count = message->hop_count;
        m->olsr_msg_tail.olsr_ipv4_msg.ttl = message->ttl;
    }

   if (DEBUG)
   {
       printf ("\nNode %d: TC Packet  size is %d\n",
           node->nodeId, outputsize);
   }

    msg->olsr_packlen = (UInt16) (outputsize);

    // Set the TC vtime to olsr->top_hold_time
    m->olsr_vtime = OlsrDouble2ME((Float32)(olsr->top_hold_time
                                                / SECOND));
    m->olsr_msgtype = TC_PACKET;

    tc->ansn = message->ansn;

    memset(&tc->reserved, 0, sizeof(UInt16));

    // Delete the list of mprs messages
    mprs = message->multipoint_relay_selector_address;

    while (mprs)
    {
        prev_mprs = mprs;
        mprs = mprs->next;
        MEM_free(prev_mprs);
    }

    OlsrSend(node, msg, outputsize, MAX_TC_JITTER, interfaceIndex);
}


// /**
// FUNCTION   :: OlsrTcForward
// LAYER      :: APPLICATION
// PURPOSE    :: Generate and send TC packet with the contents of the
//               original message "m_forward" from a received OLSR packet.
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + m_forward : olsrmsg* : TC message to be fwded
// RETURN :: void : NULL
// **/

static
void OlsrTcForward(
    Node* node,
    olsrmsg* m_forward)
{
    char packet [MAXPACKETSIZE + 1];
    olsrpacket* msg = (olsrpacket *)packet;
    olsrmsg* m = msg->olsr_msg;
    tcmsg* tc = NULL;
    tcmsg* OlsrTcForward = NULL;
    NodeAddress* mprs_ipv4_addr = NULL;
    in6_addr* mprs_ipv6_addr = NULL;
    NodeAddress* old_msg_mprs_ipv4_addr = NULL;
    in6_addr* old_msg_mprs_ipv6_addr = NULL;
    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;
    Int32 outputsize;


    if (olsr->ip_version == NETWORK_IPV6)
    {
        tc = m->olsr_ipv6_tc;
        OlsrTcForward = m_forward->olsr_ipv6_tc;
        mprs_ipv6_addr = (in6_addr *)tc->adv_neighbor_main_address;
        old_msg_mprs_ipv6_addr = (in6_addr *)OlsrTcForward->
                                                 adv_neighbor_main_address;
    }
    else

    {
        tc = m->olsr_ipv4_tc;
        OlsrTcForward = m_forward->olsr_ipv4_tc;
        mprs_ipv4_addr = (NodeAddress *)tc->adv_neighbor_main_address;
        old_msg_mprs_ipv4_addr = (NodeAddress *)OlsrTcForward->
                                                   adv_neighbor_main_address;
    }
    if (DEBUG)
    {
        printf(" Forwarding TC message \n");
    }

    if (m_forward == NULL)
    {
        return;
    }

    // Copy addresses from message to be forwarded

    if (olsr->ip_version == NETWORK_IPV6)
    {
        in6_addr* m_ipv6_addr = old_msg_mprs_ipv6_addr;
        while ((char *)m_ipv6_addr < (char *)m_forward
                                         + m_forward->olsr_msg_size)
        {
            *mprs_ipv6_addr = *m_ipv6_addr;
            mprs_ipv6_addr++;
            m_ipv6_addr++;
        }
        outputsize = (Int32)((char *)mprs_ipv6_addr - packet);
        m->olsr_msg_size = (UInt16) ((char *)mprs_ipv6_addr - (char *)m);
        m->originator_ipv6_address = m_forward->originator_ipv6_address;
        m->olsr_msg_tail.olsr_ipv6_msg.msg_seq_no =
            m_forward->olsr_msg_tail.olsr_ipv6_msg.msg_seq_no;
        m->olsr_msg_tail.olsr_ipv6_msg.hop_count =
            m_forward->olsr_msg_tail.olsr_ipv6_msg.hop_count;
        m->olsr_msg_tail.olsr_ipv6_msg.ttl =
            m_forward->olsr_msg_tail.olsr_ipv6_msg.ttl;
    }
    else

    {
        NodeAddress* m_ipv4_addr = old_msg_mprs_ipv4_addr;
        while ((char *)m_ipv4_addr < (char *)m_forward
                                         + m_forward->olsr_msg_size)
        {
            *mprs_ipv4_addr = *m_ipv4_addr;
            mprs_ipv4_addr++;
            m_ipv4_addr++;
        }
        outputsize = (Int32)((char *)mprs_ipv4_addr - packet);
        m->olsr_msg_size = (UInt16) ((char *)mprs_ipv4_addr - (char *)m);
        m->originator_ipv4_address = m_forward->originator_ipv4_address;
        m->olsr_msg_tail.olsr_ipv4_msg.msg_seq_no =
            m_forward->olsr_msg_tail.olsr_ipv4_msg.msg_seq_no;
        m->olsr_msg_tail.olsr_ipv4_msg.hop_count =
            m_forward->olsr_msg_tail.olsr_ipv4_msg.hop_count;
        m->olsr_msg_tail.olsr_ipv4_msg.ttl =
            m_forward->olsr_msg_tail.olsr_ipv4_msg.ttl;
    }

    msg->olsr_packlen = (UInt16) (outputsize);
    m->olsr_msgtype = TC_PACKET;
    m->olsr_vtime = OlsrDouble2ME((Float32)(olsr->top_hold_time
                                                / SECOND));

    tc->ansn = OlsrTcForward->ansn;
    tc->reserved = (UInt16) 0;

    RoutingOlsr* olsrData = (RoutingOlsr* ) node->appData.olsr;
    olsrData->olsrStat.numTcRelayed++;
    OlsrSendonAllInterfaces(node, msg, outputsize, MAX_TC_JITTER);
}
// /**
// FUNCTION   :: OlsrHnaForward
// LAYER      :: APPLICATION
// PURPOSE    :: Generate and send HNA packet with the contents of the
//               original message "m_forward" from a received OLSR packet.
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + m_forward : olsrmsg* : HNA message to be fwded
// RETURN :: void : NULL
// **/

static
void OlsrHnaForward(
    Node* node,
    olsrmsg* m_forward)
{
    char packet[MAXPACKETSIZE + 1];
    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;
    olsrpacket* olsr_pkt = (olsrpacket* )packet;
    olsrmsg* olsr_msg = (olsrmsg* ) olsr_pkt->olsr_msg;


    olsr->olsrStat.numHnaRelayed++;
    olsr_pkt->olsr_packlen = 2 * sizeof(UInt16) + m_forward->olsr_msg_size;

    memcpy(olsr_msg, m_forward, m_forward->olsr_msg_size);

    OlsrSendonAllInterfaces(node,
        olsr_pkt,
        olsr_pkt->olsr_packlen,
        MAX_HNA_JITTER);

    return;
}

// /**
// FUNCTION   :: OlsrUnknownMsgForward
// LAYER      :: APPLICATION
// PURPOSE    :: Forwarding the unknown message type with the contents of the
//               original message "m_forward" from a received OLSR packet.
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + m_forward : olsrmsg* : unknown message to be fwded
// RETURN :: void : NULL
// **/
static
void OlsrUnknownMsgForward(
    Node* node,
    olsrmsg* m_forward)
{
    char packet[MAXPACKETSIZE + 1];
    olsrpacket* olsr_pkt = (olsrpacket* )packet;
    olsrmsg* olsr_msg = (olsrmsg* ) olsr_pkt->olsr_msg;

    olsr_pkt->olsr_packlen = 2 * sizeof(UInt16) + m_forward->olsr_msg_size;

    memcpy(olsr_msg, m_forward, m_forward->olsr_msg_size);

    OlsrSendonAllInterfaces(node,
        olsr_pkt,
        olsr_pkt->olsr_packlen,
        MAX_HNA_JITTER);

    return;
}

// /**
// FUNCTION   :: OlsrForwardMessage
// LAYER      :: APPLICATION
// PURPOSE    :: Check if a message is to be forwarded and forward
//               it if necessary.
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + m : olsrmsg * : Pointer to message
// + originator: Address: originator of message
// + seqno : UInt16 : seq no of message
// + interfaceIndex : Int32: interface that packet arrived on
// + from_addr : Address: Neighbor Interface address that transmitted msg
// RETURN :: Int32 : 1 if msg is sent to be fwded, 0 if not
// **/

Int32
OlsrForwardMessage(
    Node* node,
    olsrmsg* m,
    Address originator,
    UInt16 seqno,
    Int32 interfaceIndex,
    Address from_addr)
{
    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;
    Address src = OlsrMidLookupMainAddr(node, from_addr);

    neighbor_entry* neighbor;
    Address ip_addr;
    ip_addr.networkType = NETWORK_IPV4;


    if(olsr->ip_version == NETWORK_IPV6)
    {
        ip_addr.networkType = NETWORK_IPV6;
        Ipv6GetGlobalAggrAddress(
                node,
                interfaceIndex,
                &ip_addr.interfaceAddr.ipv6);
    }
    else if (olsr->ip_version == NETWORK_IPV4)
    {
        ip_addr.networkType = NETWORK_IPV4;
        ip_addr.interfaceAddr.ipv4 =
                        NetworkIpGetInterfaceAddress(node,interfaceIndex);
    }
//#endif

    // Default forwarding algorithm
    // RFC 3626 Section 3.4.1

    // Lookup sender address

    if (Address_IsAnyAddress(&src))
    {
        src = from_addr;
    }

    // Condition 1
    if (NULL == (neighbor = OlsrLookupNeighborTable(node, src)))
    {

        return 0;
    }

    // Condition 1
    if (neighbor->neighbor_status != SYM)
    {
        return 0;
    }

    // Condition 2
    if (!OlsrLookupDuplicateTableFwd(node, originator, seqno, ip_addr))
    {
        return 0;
    }

    // Check if previous node is in the MPR selector set of the current
    // node

    // Condition 4
    unsigned char ttl;

    if (olsr->ip_version == NETWORK_IPV6)
    {
        ttl = m->olsr_msg_tail.olsr_ipv6_msg.ttl;
    }
    else
//#endif
    {
        ttl = m->olsr_msg_tail.olsr_ipv4_msg.ttl;
    }

    // Condition 5
    // Update duplicate table interface

    OlsrUpdateDuplicateEntry(node, originator, seqno, ip_addr);
    if (OlsrLookupMprSelectorTable(node,src) == NULL
       || ttl <= 1)
    {

        if (DEBUG)
        {
            printf(" Node is not the MPR of prev node,  don't forward\n");
        }
        return 0;
    }

    if (DEBUG)
    {
        printf(" Node is in the MPR of prev node, forward\n");
    }


    // Update dup forwarded

    OlsrSetDuplicateForward(node, originator, seqno);

    // Treat TTL hopcnt

    // Condition 6 and 7

    if (olsr->ip_version == NETWORK_IPV6)
    {
        m->olsr_msg_tail.olsr_ipv6_msg.hop_count++;
        m->olsr_msg_tail.olsr_ipv6_msg.ttl--;
    }
    else

    {
        m->olsr_msg_tail.olsr_ipv4_msg.hop_count++;
        m->olsr_msg_tail.olsr_ipv4_msg.ttl--;
    }


    // Depending upon type of message call OlsrTcForward or OlsrMidForward....

    if (m->olsr_msgtype == TC_PACKET)
    {
        OlsrTcForward(node, m);
        return 1;
    }
    else if (m->olsr_msgtype == MID_PACKET)
    {
        OlsrMidForward(node, m);
        return 1;
    }
    else if (m->olsr_msgtype == HNA_PACKET)
    {
        OlsrHnaForward(node, m);
        return 1;
    }

    else
    {
        OlsrUnknownMsgForward(node, m);
        return 0;
    }
}

// /**
// FUNCTION   :: OlsrHelloChgeStruct
// LAYER      :: APPLICATION
// PURPOSE    :: Build HELLO Message according to hello_message struct from
//               olsrmsg struct.
// PARAMETERS ::
// + node* : Node* : Pointer to Node
// + hmsg : hl_message* : Pointer to hl_message structure
// + m : olsrmsg* : Pointer to the olsrmsg
// RETURN :: void : NULL
// **/

static
void OlsrHelloChgeStruct(
    Node* node,
    hl_message* hmsg,
    olsrmsg* m)
{
    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;
    hellomsg* h;
    hellinfo* hinfo;
    hellinfo* hinf;
    NodeAddress* h_ipv4_addr;
    NodeAddress* h_ipv4_adr;
    in6_addr* h_ipv6_addr;
    in6_addr* h_ipv6_adr;
    hello_neighbor* nb;

    hmsg->neighbors = (hello_neighbor *)NULL;

    if (!m)
    {
        return;
    }

    if (m->olsr_msgtype != HELLO_PACKET)
    {
        return;
    }

    // parse olsr message and collects all information in hl_message

    if (olsr->ip_version == NETWORK_IPV6)
    {
        h = m->olsr_ipv6_hello;
        hinfo = h->hell_info;
        SetIPv6AddressInfo(&hmsg->source_addr, m->originator_ipv6_address);
        hmsg->packet_seq_number = m->olsr_msg_tail.olsr_ipv6_msg.msg_seq_no;
    }
    else

    {
        h = m->olsr_ipv4_hello;
        hinfo = h->hell_info;
        SetIPv4AddressInfo(&hmsg->source_addr, m->originator_ipv4_address);
        hmsg->packet_seq_number = m->olsr_msg_tail.olsr_ipv4_msg.msg_seq_no;
    }


     // Get vtime
    hmsg->vtime = OlsrME2Double(m->olsr_vtime);

    // Get htime
    hmsg->htime = OlsrME2Double(h->htime);

    // Willingness
    hmsg->willingness = h->willingness;

    if (DEBUG)
    {
        printf(" Hello message size is %d\n", m->olsr_msg_size);
    }

    for (hinf = hinfo; (char *)hinf < (char *)m + m->olsr_msg_size;
         hinf = (hellinfo *)((char *)hinf + hinf->link_msg_size))
    {
        if (DEBUG)
        {
            printf(" Link message size is %d\n", hinf->link_msg_size);
        }

        if (olsr->ip_version == NETWORK_IPV6)
        {
            h_ipv6_addr = (in6_addr *)hinf->neigh_addr;
            h_ipv6_adr = h_ipv6_addr;

            while ((char *)h_ipv6_adr < (char *)hinf + hinf->link_msg_size)
            {
                nb = (hello_neighbor *) MEM_malloc(sizeof(hello_neighbor));
                memset(nb, 0, sizeof(hello_neighbor));

                if (nb == 0)
                {
                    printf("olsrd: out of memery \n");
                    break;
                }

                SetIPv6AddressInfo(&nb->address, *h_ipv6_adr);
                nb->link = EXTRACT_LINK(hinf->link_code);
                nb->status = EXTRACT_STATUS(hinf->link_code);

                if (DEBUG)
                {
                    char addrString[MAX_STRING_LENGTH];
                    IO_ConvertIpAddressToString(&nb->address,
                    addrString);

                    printf(" Neighbor adress in hello is %s Link: %d ,"
                       " Status: %d \n", addrString, nb->link, nb->status);
                }

                nb->next = hmsg->neighbors;
                hmsg->neighbors = nb;

                h_ipv6_adr++;
            }

        }
        else

        {
            h_ipv4_addr = (NodeAddress *)hinf->neigh_addr;
            h_ipv4_adr = h_ipv4_addr;

            while ((char *)h_ipv4_adr < (char *)hinf + hinf->link_msg_size)
            {
                nb = (hello_neighbor *) MEM_malloc(sizeof(hello_neighbor));
                memset(nb, 0, sizeof(hello_neighbor));

                if (nb == 0)
                {
                    printf("olsrd: out of memery \n");
                    break;
                }

                SetIPv4AddressInfo(&nb->address, *h_ipv4_adr);
                nb->link = EXTRACT_LINK(hinf->link_code);
                nb->status = EXTRACT_STATUS(hinf->link_code);

                if (DEBUG)
                {
                    char addrString[MAX_STRING_LENGTH];
                    IO_ConvertIpAddressToString(&nb->address,
                    addrString);

                    printf(" Neighbor adress in hello is %s Link: %d ,"
                        " Status: %d \n", addrString, nb->link, nb->status);
                }

                nb->next = hmsg->neighbors;
                hmsg->neighbors = nb;

                h_ipv4_adr++;
            }
        }
    }
}

// /**
// FUNCTION   :: OlsrTcChgeStruct
// LAYER      :: APPLICATION
// PURPOSE    :: Build TC Message according to tc_message struct from
//               olsrmsg struct.
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + tmsg : tc_message * : Pointer to the TC message
// + m : olsrmsg* : OLSR message pointer
// + from_addr: Address: Neighbor interface address that transmitted TC
// RETURN :: void : NULL
// **/

static
void OlsrTcChgeStruct(
    Node* node,
    tc_message* tmsg,
    olsrmsg* m,
    Address from_addr)
{
    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;
    tcmsg* tc;
    NodeAddress* mprs_ipv4_addr = NULL;
    in6_addr* mprs_ipv6_addr = NULL;
    NodeAddress* m_ipv4_addr;
    in6_addr* m_ipv6_addr;
    tc_mpr_addr* mprs;
    Address tmp_addr = OlsrMidLookupMainAddr(node, from_addr);

    tmsg->multipoint_relay_selector_address = (tc_mpr_addr *) NULL;

    if (!m)
    {
        return;
    }

    if (m->olsr_msgtype != TC_PACKET)
    {
        return;
    }

    // parse olsr message and collects all information in tc_message

    if (olsr->ip_version == NETWORK_IPV6)
    {
        tc = m->olsr_ipv6_tc;
        mprs_ipv6_addr = (in6_addr *)tc->adv_neighbor_main_address;
    }
    else

    {
        tc = m->olsr_ipv4_tc;
        mprs_ipv4_addr = (NodeAddress *)tc->adv_neighbor_main_address;
    }

    if (Address_IsAnyAddress(&tmp_addr))
    {
        tmsg->source_addr = from_addr;
    }
    else
    {
       tmsg->source_addr = tmp_addr;
    }

    tmsg->vtime = OlsrME2Double(m->olsr_vtime);
    tmsg->ansn = tc->ansn;

    if (olsr->ip_version == NETWORK_IPV6)
    {
        SetIPv6AddressInfo(&tmsg->originator, m->originator_ipv6_address);

        tmsg->packet_seq_number = m->olsr_msg_tail.olsr_ipv6_msg.msg_seq_no;
        tmsg->hop_count =  m->olsr_msg_tail.olsr_ipv6_msg.hop_count;

        m_ipv6_addr = mprs_ipv6_addr;
        while ((char *)m_ipv6_addr < (char *)m + m->olsr_msg_size)
        {
            mprs = (tc_mpr_addr *)MEM_malloc(sizeof(tc_mpr_addr));

            memset(mprs, 0, sizeof(tc_mpr_addr));

            if (mprs == 0)
            {
                printf("olsrd: out of memery \n");
                break;
            }

            SetIPv6AddressInfo(&mprs->address, *m_ipv6_addr);
            mprs->next = tmsg->multipoint_relay_selector_address;
            tmsg->multipoint_relay_selector_address = mprs;

            m_ipv6_addr++;
        }
    }
    else

    {
        SetIPv4AddressInfo(&tmsg->originator, m->originator_ipv4_address);
        tmsg->packet_seq_number = m->olsr_msg_tail.olsr_ipv4_msg.msg_seq_no;
        tmsg->hop_count =  m->olsr_msg_tail.olsr_ipv4_msg.hop_count;
        m_ipv4_addr = mprs_ipv4_addr;
        while ((char *)m_ipv4_addr < (char *)m + m->olsr_msg_size)
        {
            mprs = (tc_mpr_addr *)MEM_malloc(sizeof(tc_mpr_addr));

            memset(mprs, 0, sizeof(tc_mpr_addr));

            if (mprs == 0)
            {
                printf("olsrd: out of memery \n");
                break;
            }

            SetIPv4AddressInfo(&mprs->address, *m_ipv4_addr);
            mprs->next = tmsg->multipoint_relay_selector_address;
            tmsg->multipoint_relay_selector_address = mprs;

            m_ipv4_addr++;
        }
    }
}


/***************************************************************************
 *             Definition of message handling functions                    *
 ***************************************************************************/

// /**
// FUNCTION   :: OlsrBuildTcPacket
// LAYER      :: APPLICATION
// PURPOSE    :: Build tc message
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + message : tc_message * : Pointer to TC message data structure
// RETURN :: Int32 : 0 if message to be sent, -1 if not
// **/

static
Int32 OlsrBuildTcPacket(
    Node* node,
    tc_message* message)
{
    tc_mpr_addr* message_mpr;
    mpr_selector_entry* mprs;
    mpr_selector_hash_type* mprs_hash;

    unsigned char index;
    bool empty_packet=true;
    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;
    Address addr_ip = olsr->main_address;


    message->multipoint_relay_selector_address = NULL;
    message->packet_seq_number = 0;

    message->hop_count = 0;
    message->ttl = MAX_TTL;

    message->ansn = olsr->mprstable.ansn;

    message->originator = addr_ip;
    message->source_addr = addr_ip;

    for (index = 0; index < HASHSIZE; index++)
    {
        mprs_hash = &olsr->mprstable.mpr_selector_hash[index];

        for (mprs = mprs_hash->mpr_selector_forw;
            mprs != (mpr_selector_entry *)mprs_hash;
            mprs = mprs->mpr_selector_forw)
        {
            message_mpr = (tc_mpr_addr *) MEM_malloc(sizeof(tc_mpr_addr));

            memset(message_mpr, 0, sizeof(tc_mpr_addr));

            message_mpr->address = mprs->mpr_selector_main_addr;
            message_mpr->next = message->multipoint_relay_selector_address;
            message->multipoint_relay_selector_address = message_mpr;
            empty_packet=false;
        }
    }

    // To handle the empty packet case..
    // Keep sending empty tc till vtime of previous TC message is valid
    // After that time, don't send till non empty set occurs

    if (empty_packet == true)
    {
        if (olsr->tc_valid_time > getSimTime(node))
        {
            return 0;
        }
        else
        {
            return -1;
        }
    }
    else
    {
        olsr->tc_valid_time = getSimTime(node) + olsr->top_hold_time;
        return 0;
    }
}

// /**
// FUNCTION   :: OlsrGenerateTc
// LAYER      :: APPLICATION
// PURPOSE    :: Generate tc message
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + interfaceIndex : Int32 : outgoing interface
// RETURN :: void : NULL
// **/

static
void OlsrGenerateTc(
    Node* node,
    Int32 interfaceIndex)
{
    tc_message tcpacket;
    Int32 send_message;
    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    // If this node is selected MPR by others, then only TC message is
    // generated, otherwise stop the generation of TC message. It will
    // be again activated when the node will be MPR again.

    if (OlsrExistMprSelectorTable(node))
    {

        // receive tc packet info from the node structure to tc_message
        // structure. If empty mpr selector set and validity time of prev
        // tc expired, don't send tc message

        send_message = OlsrBuildTcPacket(node, &tcpacket);

        if (send_message!=-1)
        {
            // printf("Generate Tc send_message\n");
               // prepare the tc message and send
            OlsrSendTc(node, &tcpacket, interfaceIndex);
        }
        else
        {
            if (DEBUG)
            {
                printf ("Validation time expires. ");
                printf ("Returning without any TC generation.\n");
            }
        }
    }
    else
    {
        if (DEBUG)
        {
            printf ("No entry in MPR Selection Table. ");
            printf ("Returning without any TC generation.\n");
        }
        // printf("Generate Tc tcMessageStarted = FALSE\n");
        olsr->tcMessageStarted = FALSE;
    }
}


// /**
// FUNCTION   :: OlsrLookupMprStatus
// LAYER      :: APPLICATION
// PURPOSE    :: Function looks up hello message if the current node
//               status is MPR or not
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + message : hl_message *: Pointer to hello message
// + incomingInterface: Int32 : interface on which hello message arrived
// RETURN :: Int32 : 1  if node is MPR, 0 if not
// **/


static
Int32 OlsrLookupMprStatus(
    Node* node,
    hl_message* message,
    Int32 incomingInterface)
{
    hello_neighbor* neighbors;
    neighbors = message->neighbors;
    Address interfaceAddress;
    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;


    if(olsr->ip_version == NETWORK_IPV6)
    {
        interfaceAddress.networkType = NETWORK_IPV6;
        Ipv6GetGlobalAggrAddress(
                node,
                incomingInterface,
                &interfaceAddress.interfaceAddr.ipv6);
    }
    else if (olsr->ip_version == NETWORK_IPV4)
    {
        interfaceAddress.networkType = NETWORK_IPV4;
        interfaceAddress.interfaceAddr.ipv4 =
                        NetworkIpGetInterfaceAddress(node,incomingInterface);
    }
//#endif


    while (neighbors != NULL)
    {
        if (Address_IsSameAddress(&neighbors->address, &interfaceAddress))
        {
            if ((neighbors->link == SYM_LINK)
                 && (neighbors->status == MPR_NEIGH))
            {
                return 1;
            }
            else
            {
                return 0;
            }
        }
        neighbors = neighbors->next;
    }
    return 0;
}

// /**
// FUNCTION   :: OlsrProcessReceivedHello
// LAYER      :: APPLICATION
// PURPOSE    :: Process hello message
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + message : hl_message * : Pointer to hello message
// + incomingInterface: Int32: interface at which packet arrived
// + from_addr: Address: neighbor interface address that sent packet
// RETURN :: Int32 : 1 if error
// **/

static
Int32 OlsrProcessReceivedHello(
    Node* node,
    hl_message* message,
    Int32 incomingInterface,
    Address from_addr)
{
    link_entry* link;
    neighbor_entry* neighbor;

    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;
    Address addr_ip;
    addr_ip.networkType = NETWORK_IPV4;

    if(olsr->ip_version == NETWORK_IPV6)
    {
        addr_ip.networkType = NETWORK_IPV6;
        Ipv6GetGlobalAggrAddress(
                node,
                incomingInterface,
                &addr_ip.interfaceAddr.ipv6);
    }
    else if (olsr->ip_version == NETWORK_IPV4)
    {
        addr_ip.networkType = NETWORK_IPV4;
        addr_ip.interfaceAddr.ipv4 =
                        NetworkIpGetInterfaceAddress(node,incomingInterface);
    }
//#endif

    if (DEBUG)
    {
        char addrString[MAX_STRING_LENGTH];
        IO_ConvertIpAddressToString(&from_addr,
                addrString);

        char strTime[MAX_STRING_LENGTH];
        ctoa(getSimTime(node), strTime);
        printf("Node %d receives HELLO message from %s"
            " on interface %d at %s\n",
            node->nodeId, addrString, incomingInterface, strTime);

        OlsrPrintHelloMessage(message);
    }

    olsr->olsrStat.numHelloReceived++;

    if (message == NULL)
    {
        return 1;
    }

	if (SYMMETRIC_TOPOLOGY_TABLE)
	{

		clear_tco_node_addr_set(&(olsr->recent_delete_list));
		clear_tco_node_addr_set(&(olsr->recent_add_list));

		olsr->bNeighborChgCausedRemoveFromHigherHop = FALSE;
	}

	if (SYMMETRIC_TOPOLOGY_TABLE)
	{
		//
		olsr->naRecentChangedAddressByTC = from_addr.interfaceAddr.ipv4;

		/*
		char timeStr[MAX_STRING_LENGTH];
		TIME_PrintClockInSecond(getSimTime(node), timeStr, node);

		double dSimTime = atof(timeStr);

		if (dSimTime > 10)
		{
			DebugBreak();
		}

		*/

		
	}


    // RFC 3626 Section 7.1.1

    // Update Link Status
    // OlsrPrintLinkSet(node);

    link = OlsrUpdateLinkEntry(node,
               addr_ip, from_addr, message, incomingInterface);

    neighbor = link->neighbor;

    // RFC 3626 Section 8.1.1

    // Update neighbor willingness if different

    if (neighbor->neighbor_willingness != message->willingness)
    {
          //If willingness changed - recalculate
          neighbor->neighbor_willingness = message->willingness;

          // This flag is set to UP to recalculate MPR set/routing table

		  g_iNeighborChgByOlsrProcessReceivedHello++;

		  //Peter Comment: this change only related to mpr re-calculation, so skip it
		  
          olsr->changes_neighborhood = TRUE;
          olsr->changes_topology = TRUE;

		  g_iTopologyChgByOlsrProcessReceivedHello++;

    }

    // RFC 3626 Section 8.2.1
    // Don't register neighbors of neighbors that announces WILL_NEVER

    if (neighbor->neighbor_willingness != WILL_NEVER)
    {
        // Processing the list of neighbors in the received message
        OlsrProcessNeighborsInHelloMsg(node, neighbor, message);
    }

    // RFC 3626 Section 8.4.1
    // Check if we are chosen as MPR

    if (OlsrLookupMprStatus(node, message, incomingInterface))
    {
        // source_addr is always the main addr of a node!
        OlsrUpdateMprSelectorTable(node,
            message->source_addr, (float)message->vtime);
    }

    // Process changes immedeatly in case of MPR updates
    OlsrDestroyHelloMessage(message);
    

	char szTextRT[32768] = {0};

	BOOL bRTPrinted = FALSE;

	if (SYMMETRIC_TOPOLOGY_TABLE)
	{
		
		if (olsr->recent_add_list != NULL || olsr->recent_delete_list != NULL)
		{
			
			
			
			//if (iRTAddOrDelete == 2 && node->nodeId == 2 && olsr->naRecentChangedAddressByTC == 8 && olsr->recent_delete_list != NULL)
			//if (iRTAddOrDelete == 2)
			//if (FALSE)
			//if (olsr->recent_delete_list != NULL && node->nodeId == 8)
			//if (olsr->recent_delete_list != NULL)
			//if (g_iChaseRouteTable == 1 && node->nodeId == 30 && olsr->recent_delete_list == NULL && olsr->naRecentChangedAddressByTC == 29)
			if (g_iChaseRouteTable == 1)
			{

				
				//printf("node->nodeId == 8 && iRTAddOrDelete == 2 && olsr->naRecentChangedAddressByTC == 10 %f \n", dSimTime);
				
				bRTPrinted = TRUE;

				memset(szTextRT, 0, 32768 * sizeof(char));
				PeterChaseTableChg(node, szTextRT, TRUE);
				//DebugBreak();
				//DebugBreak();
			}
		}
	}
	
	
	OlsrProcessChanges(node);

	if (SYMMETRIC_TOPOLOGY_TABLE)
	{

		clear_tco_node_addr_set(&(olsr->recent_delete_list));
		clear_tco_node_addr_set(&(olsr->recent_add_list));

		olsr->bNeighborChgCausedRemoveFromHigherHop = FALSE;
	}

	if (g_iChaseRouteTable && bRTPrinted)
	{
		PeterChaseTableChg(node, szTextRT, FALSE);
	}

    if (DEBUG)
    {
        OlsrPrintNeighborTable(node);
        OlsrPrint2HopNeighborTable(node);
        OlsrPrintMprSelectorTable(node);
    }

    return 0;
}

// /**
// FUNCTION   :: OlsrProcessReceivedHna
// LAYER      :: APPLICATION
// PURPOSE    :: Process received hna msg
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + message : hna_message* : Pointer to HNA msg
// + source_addr : Address : source address of the msg
// + incomingInterface : Int32 : Incoming Interface Index
// + m : olsrmsg* : Pointer to a generic olsr msg
// RETURN :: Int32 : Returns zero only if the hna msg is processed
// **/
static
Int32 OlsrProcessReceivedHna(
    Node* node,
    hna_message* message,
    Address source_addr,
    Int32 incomingInterface,
    olsrmsg* m)
{
    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;
    Address addr_ip;


    if(olsr->ip_version == NETWORK_IPV6)
    {
        addr_ip.networkType = NETWORK_IPV6;
        Ipv6GetGlobalAggrAddress(
                node,
                incomingInterface,
                &addr_ip.interfaceAddr.ipv6);
    }
    else if (olsr->ip_version == NETWORK_IPV4)
    {
        addr_ip.networkType = NETWORK_IPV4;
        addr_ip.interfaceAddr.ipv4 =
                        NetworkIpGetInterfaceAddress(node,incomingInterface);
    }
//#endif
    //neighbor_entry* neighbor;

    olsr->olsrStat.numHnaReceived++;

    if (DEBUG)
    {
        OlsrPrintHnaMessage(node, message);
    }

    // we should not check the originator address
    if (Address_IsSameAddress(&message->hna_origaddr, &addr_ip))
    {
        OlsrDestroyHnaMessage(message);
        return 1;
    }

    // Check whether the hna_msg is received from a sym neighbor or not
    if (OlsrCheckLinktoNeighbor(node, source_addr) != SYM_LINK)
    {
        // The hna_msg's source address is not in the neighbor table
        OlsrDestroyHnaMessage(message);
        return 1;
    }

    if (NULL != OlsrLookupDuplicateTableProc(node,
                    message->hna_origaddr, message->hna_seqno))
    {
        OlsrForwardMessage(node,
            m,
            message->hna_origaddr,
            message->hna_seqno,
            incomingInterface,
            source_addr);

        OlsrDestroyHnaMessage(message);
        return 1;
    }


    hna_net_addr*  hna_net_pair = message->hna_net_pair;

    while (hna_net_pair)
    {
        OlsrUpdateHnaEntry(node,
            message->hna_origaddr,
            hna_net_pair->net,
            hna_net_pair->netmask,
            message->vtime);

        hna_net_pair = hna_net_pair->next;
    }

    OlsrForwardMessage(node,
        m,
        message->hna_origaddr,
        message->hna_seqno,
        incomingInterface,
        source_addr);

    OlsrDestroyHnaMessage(message);

    // To allow routing table to incorporate HNA insertions
    OlsrProcessChanges(node);

    return 0;
}

// /**
// FUNCTION   :: OlsrHnaChgeStruct
// LAYER      :: APPLICATION
// PURPOSE    :: Parse an olsr message and collects all information
//               in HNA msg
// PARAMETERS ::
// + node : Node* : Pointer to Node
// + hna_msg : hna_message* : Pointer to HNA msg
// + m : olsrmsg* : Pointer to a generic olsr msg
// RETURN :: void : NULL
// **/
static
void OlsrHnaChgeStruct(
    Node* node,
    hna_message* hna_msg,
    olsrmsg* m)
{
    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;
    hnamsg* hna;
    struct _hnapair_ipv6* hna_pair_ipv6 = NULL;
    struct _hnapair_ipv4* hna_pair_ipv4 = NULL;

    if (!m)
    {
        return;
    }
    if (m->olsr_msgtype != HNA_PACKET)
    {
        return;
    }

    // parse olsr message and collects all information in mid_message

    if (olsr->ip_version == NETWORK_IPV6)
    {
        SetIPv6AddressInfo(&hna_msg->hna_origaddr,
            m->originator_ipv6_address);  // originator's address
        hna = m->olsr_ipv6_hna;
        hna_pair_ipv6 = (struct _hnapair_ipv6* )hna->hna_net_pair;
    }
    else

    {
        SetIPv4AddressInfo(&hna_msg->hna_origaddr,
            m->originator_ipv4_address);  // originator's address
        hna = m->olsr_ipv4_hna;
        hna_pair_ipv4 = (struct _hnapair_ipv4* )hna->hna_net_pair;
    }
    hna_msg->vtime = OlsrME2Double(m->olsr_vtime); // validity time
    hna_msg->hna_net_pair = NULL;  // alias address

    hna_net_addr* hna_pair_entry;

    if (olsr->ip_version == NETWORK_IPV6)
    {
        // number of hops to destination
        hna_msg->hna_hopcnt = m->olsr_msg_tail.olsr_ipv6_msg.hop_count;
        hna_msg->hna_ttl = MAX_TTL;       // ttl
        // sequence number
        hna_msg->hna_seqno = m->olsr_msg_tail.olsr_ipv6_msg.msg_seq_no;
        while ((char *)hna_pair_ipv6 < (char *)m + m->olsr_msg_size)
        {
            hna_pair_entry = (hna_net_addr* )
                                 MEM_malloc(sizeof(hna_net_addr));

            memset(hna_pair_entry, 0, sizeof(hna_net_addr));

            if (hna_pair_entry == NULL)
            {
                printf("olsrd: out of memery \n");
                break;
            }
            SetIPv6AddressInfo(&hna_pair_entry->net, hna_pair_ipv6->addr);
            hna_pair_entry->netmask.v6 = hna_pair_ipv6->netmask.s6_addr32[3];
            hna_pair_entry->next = hna_msg->hna_net_pair;
            hna_msg->hna_net_pair = hna_pair_entry;
            hna_pair_ipv6++;
        }
    }
    else

    {
        hna_msg->hna_hopcnt = m->olsr_msg_tail.olsr_ipv4_msg.hop_count;
        hna_msg->hna_ttl = MAX_TTL;       // ttl
        hna_msg->hna_seqno = m->olsr_msg_tail.olsr_ipv4_msg.msg_seq_no;
        while ((char *)hna_pair_ipv4 < (char *)m + m->olsr_msg_size)
        {
            hna_pair_entry = (hna_net_addr* )
                                 MEM_malloc(sizeof(hna_net_addr));

            memset(hna_pair_entry, 0, sizeof(hna_net_addr));

            if (hna_pair_entry == NULL)
            {
                printf("olsrd: out of memery \n");
                break;
            }
            SetIPv4AddressInfo(&hna_pair_entry->net, hna_pair_ipv4->addr);
            hna_pair_entry->netmask.v4 = hna_pair_ipv4->netmask;
            hna_pair_entry->next = hna_msg->hna_net_pair;
            hna_msg->hna_net_pair = hna_pair_entry;
            hna_pair_ipv4++;
        }
    }
    return;
}



// /**
// FUNCTION   :: OlsrProcessReceivedMid
// LAYER      :: APPLICATION
// PURPOSE    :: Process received mid msg
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + message : mid_message* : Pointer to MID msg
// + source_addr : Address : source address of the msg
// + incomingInterface : Int32 : Incoming Interface Index
// + m : olsrmsg* : Pointer to a generic olsr msg
// RETURN :: Int32 : Returns zero only if the mid msg is processed
// **/
static
Int32 OlsrProcessReceivedMid(
    Node* node,
    mid_message* message,
    Address source_addr,
    Int32 incomingInterface,
    olsrmsg* m)
{
    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;
    Address addr_ip;


    if(olsr->ip_version == NETWORK_IPV6)
    {
        addr_ip.networkType = NETWORK_IPV6;
        Ipv6GetGlobalAggrAddress(
                node,
                incomingInterface,
                &addr_ip.interfaceAddr.ipv6);
    }
    else if (olsr->ip_version == NETWORK_IPV4)
    {
        addr_ip.networkType = NETWORK_IPV4;
        addr_ip.interfaceAddr.ipv4 =
                        NetworkIpGetInterfaceAddress(node,incomingInterface);
    }
//#endif

    olsr->olsrStat.numMidReceived++;

    if (message == NULL)
    {
        return 1;
    }

    if (DEBUG)
    {
        char addrString[MAX_STRING_LENGTH];
        IO_ConvertIpAddressToString(&source_addr,
                addrString);

        char strTime[MAX_STRING_LENGTH];
        ctoa(getSimTime(node), strTime);
        printf("Node %d receives MID message from %s"
            " on interface %d at %s\n",
            node->nodeId, addrString, incomingInterface, strTime);

        OlsrPrintMidMessage(message);
    }

    // we should not check the originator address
    if (Address_IsSameAddress(&message->mid_origaddr, &addr_ip))
    {
        OlsrDestroyMidMessage(message);
        return 1;
    }

    // Check whether the mid_msg is received from a sym neighbor or not
    if (OlsrCheckLinktoNeighbor(node, source_addr) != SYM_LINK)
    {
        // The mid_message's source address is not in the neighbor table
        OlsrDestroyMidMessage(message);
        return 1;
    }

    if (NULL != OlsrLookupDuplicateTableProc(node,
                    message->mid_origaddr, message->mid_seqno))
    {
        OlsrForwardMessage(node,
            m,
            message->mid_origaddr,
            message->mid_seqno,
            incomingInterface,
            source_addr);

        OlsrDestroyMidMessage(message);
        return 1;
    }

    mid_alias* mid_addr = message->mid_addr;
    while (mid_addr)
    {
        Address main_addr = OlsrMidLookupMainAddr(node,
                                mid_addr->alias_addr);
        if (!Address_IsAnyAddress(&main_addr))
        {
            // already exists in the mid-table, so just update the
            // timer associated with mid_table_entry

            OlsrUpdateMidTable(node, main_addr, message->vtime);
        }
        else
        {
            OlsrInsertMidAlias(node,
                message->mid_origaddr,
                mid_addr->alias_addr,
                message->vtime);

            // We add a Mid entry,
            // should recalculate RT

            olsr->changes_topology = TRUE;

			g_iTopologyChgByOlsrProcessReceivedMid++;
        }
        mid_addr = mid_addr->next;
    }

    OlsrForwardMessage(node,
        m,
        message->mid_origaddr,
        message->mid_seqno,
        incomingInterface,
        source_addr);

    OlsrDestroyMidMessage(message);

    // To allow routing table to incorporate MID insertions
    OlsrProcessChanges(node);

    return 0;
}





void PeterChaseTableChg(Node* node, char * szTextRT, BOOL bNotPartialPrint)
{
	//char szTextRT[32768] = {0};
	//memset(szTextRT, 0, 32768 * sizeof(char));

	RoutingOlsr *olsr = (RoutingOlsr* ) node->appData.olsr;


	if (bNotPartialPrint)
	{
		int iRTAddOrDelete = 0;
		if (olsr->recent_add_list != NULL)
		{
			iRTAddOrDelete = iRTAddOrDelete + 1;
		}

		if (olsr->recent_delete_list != NULL)
		{

			iRTAddOrDelete = iRTAddOrDelete + 2;
		}


		
		sprintf(szTextRT, "\n");
		sprintf(szTextRT, "%s****************************************************************************************** \n", szTextRT);

		char timeStr[MAX_STRING_LENGTH];
		TIME_PrintClockInSecond(getSimTime(node), timeStr, node);

		double dSimTime = atof(timeStr);

		
		
		
		
		
		int iNeighborChg = 0;

		if (olsr->changes_neighborhood)
		{
			iNeighborChg = 1;
		}
		

		
		
		if (node->nodeId == 71 && iRTAddOrDelete == 1 && olsr->naRecentChangedAddressByTC == 81 && iNeighborChg == 1 
			&& olsr->bNeighborChgCausedRemoveFromHigherHop == 1 && dSimTime > 19 && dSimTime < 21)
		{
			//DebugBreak();
		}
		
		
		

		//double dInMS = dSimTime * 1000.0;

		sprintf(szTextRT, "%sFor node->nodeId = %d, iRTAddOrDelete = %d, olsr->naRecentChangedAddressByTC = %d, iNeighborChg = %d, olsr->bNeighborChgCausedRemoveFromHigherHop = %d, at time %f S: \n", 
			szTextRT, node->nodeId, iRTAddOrDelete, olsr->naRecentChangedAddressByTC, iNeighborChg, olsr->bNeighborChgCausedRemoveFromHigherHop, dSimTime);
	}
	else
	{

		sprintf(szTextRT, "%s\n After OlsrProcessChanges for node %d \n", szTextRT, node->nodeId);

	}
	

	

	OlsrPrintRoutingTable(olsr->routingtable);

	sprintf(szTextRT, "%s%s", szTextRT, g_szTextRT);
	
	//sprintf(szTextRT, "%solsr->naRecentChangedAddressByTC = %d \n", szTextRT, olsr->naRecentChangedAddressByTC);

	/*
	if (olsr->naRecentChangedAddressByTC == 10)
	{

		//DebugBreak();
	}
	*/




	if (bNotPartialPrint)
	{

		tco_node_addr * tco_add_list_tmp = olsr->recent_add_list;

		sprintf(szTextRT, "%sadd_list: ", szTextRT);

		while (tco_add_list_tmp != NULL)
		{

			sprintf(szTextRT, "%stco_add_list_tmp->nid = %d  ", szTextRT, tco_add_list_tmp->nid);

			tco_add_list_tmp = tco_add_list_tmp->next;
		}

		sprintf(szTextRT, "%s\n", szTextRT);

		tco_node_addr * tco_delete_list_tmp = olsr->recent_delete_list;



		//if (node->nodeId == 8 && olsr->naRecentChangedAddressByTC == 11 && tco_delete_list_tmp != NULL)
		{
			//DebugBreak();
		}

		sprintf(szTextRT, "%sdelete_list: ", szTextRT);

		while (tco_delete_list_tmp != NULL)
		{

			sprintf(szTextRT, "%stco_delete_list_tmp->nid = %d  ", szTextRT, tco_delete_list_tmp->nid);

			tco_delete_list_tmp = tco_delete_list_tmp->next;
		}

		sprintf(szTextRT, "%s\n", szTextRT);

		OlsrPrintNeighborTable(node);

		sprintf(szTextRT, "%s%s", szTextRT, g_szTextRT);

		sprintf(szTextRT, "%s\n", szTextRT);

		OlsrPrint2HopNeighborTable(node);

		sprintf(szTextRT, "%s%s", szTextRT, g_szTextRT);

		sprintf(szTextRT, "%s\n", szTextRT);


		OlsrPrintTopologyTableSYM(node);

		sprintf(szTextRT, "%s%s", szTextRT, g_szTextRT);
	}
	else
	{
		FILE* fp = NULL;

		char sTmp[MAX_PATH] = {0};

		ZeroMemory(sTmp, MAX_PATH * sizeof(char));

		sprintf(sTmp, "Speed-%d", g_iMobilitySpeed);

		if (_OLSR_MULTIPATH)
		{

			sprintf(sTmp, "%s-%s-TraceRT_MP", sTmp, g_szRoot);

		}
		else
		{

			sprintf(sTmp, "%s-%s-TraceRT_SP", sTmp, g_szRoot);

		}

		sprintf(sTmp, "%s_ARC_%d", sTmp, g_iAccumulativeRouteCalculation);


		fp = fopen(sTmp, "a");

		if (!fp)
		{
			ERROR_ReportError("Can't open EstimateTimeComplexity \n");
		}
		else
		{


			fprintf(fp, "%s", szTextRT);
			fclose(fp);
		}
	}

	

}






// /**
// FUNCTION   :: OlsrProcessReceivedTc
// LAYER      :: APPLICATION
// PURPOSE    :: Process tc message
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + message : tc_message*: Pointer to TC message
// + source_addr: Address: Address of sender
// + incomingInterface: Int32: incoming interface
// + m: olsrmsg*: olsr message pointer
// RETURN :: Int32 : 1 if error, else 0
// **/






static
Int32 OlsrProcessReceivedTc(
    Node* node,
    tc_message* message,
    Address source_addr,
    Int32 incomingInterface,
    olsrmsg* m)
{

	//Peter Comment:add for debug
	
	char timeStr[MAX_STRING_LENGTH];
	TIME_PrintClockInSecond(getSimTime(node), timeStr, node);

	double dSimTime = atof(timeStr);
	
	
	/*
	if (node->nodeId == 1)
	{
		DebugBreak();
	}
	*/


	
	
	topology_last_entry *t_last;

    RoutingOlsr *olsr = (RoutingOlsr* ) node->appData.olsr;
    Address addr_ip;


    if(olsr->ip_version == NETWORK_IPV6)
    {
        addr_ip.networkType = NETWORK_IPV6;
        Ipv6GetGlobalAggrAddress(
                node,
                incomingInterface,
                &addr_ip.interfaceAddr.ipv6);
    }
    else if (olsr->ip_version == NETWORK_IPV4)
    {
        addr_ip.networkType = NETWORK_IPV4;
        addr_ip.interfaceAddr.ipv4 =
                        NetworkIpGetInterfaceAddress(node,incomingInterface);
    }


    olsr->olsrStat.numTcReceived++;

    if (message == NULL)
    {
        return 1;
    }

	//Peter modified for testing
    //if (node->nodeId == 18 && dSimTime > 15.91 && dSimTime < 15.97 && source_addr.interfaceAddr.ipv4 == 34 && message->originator.interfaceAddr.ipv4 == 31)
	//if (node->nodeId == 20 && dSimTime > 28.0 && dSimTime < 35.0)
    if (DEBUG)
    {

		//DebugBreak();
		printf("||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||\n\n");

		g_iChaseRouteTable = 0;
		OlsrPrint2HopNeighborTable(node);
		//OlsrPrintTopologyTableSYM(node);
		g_iChaseRouteTable = 1;

        char addrString[MAX_STRING_LENGTH];
        IO_ConvertIpAddressToString(&source_addr,
                addrString);

        char strTime[MAX_STRING_LENGTH];
        ctoa(getSimTime(node), strTime);
        printf("Node %d receives TC message from %s"
            " on interface %d at %s\n",
            node->nodeId, addrString, incomingInterface, strTime);

        OlsrPrintTcMessage(message);
    }


    // we should not check the originator address
    if (Address_IsSameAddress(&message->originator, &addr_ip))
    {
        OlsrDestroyTcMessage(message);
        return 1;
    }

    // if originator address already in duplicate table proc
    // then ignore message processing and fwd

    if (NULL != OlsrLookupDuplicateTableProc(node,
                    message->originator, message->packet_seq_number))
    {
        OlsrForwardMessage(node, m,
        message->originator,message->packet_seq_number,
        incomingInterface,source_addr);

        OlsrDestroyTcMessage(message);
        return 1;
    }

    // Section 9.5 Condition 1
    // Check whether the tc is received from a sym neighbor or not

    if (OlsrCheckLinktoNeighbor(node, source_addr) != SYM_LINK)
    {
        OlsrDestroyTcMessage(message);
        return 1;
    }

    if (DEBUG)
    {
        tc_mpr_addr* mpr;
        char strTime[MAX_STRING_LENGTH];
        char addrString[MAX_STRING_LENGTH];

        IO_ConvertIpAddressToString(&source_addr,
            addrString);

        ctoa(getSimTime(node), strTime);

        printf("Node %d receives tc message from %s at %s\n",
            node->nodeId, addrString, strTime);

        mpr = message->multipoint_relay_selector_address;
        printf("mpr_selector_list:[");
        while (mpr != NULL)
        {
            IO_ConvertIpAddressToString(&mpr->address,
                addrString);

            printf("%s:", addrString);
            mpr = mpr->next;
        }
        printf("]\n");
    }

	// Peter comment: add for debuging
	/*
	if (node->nodeId == 1 && message->originator.interfaceAddr.ipv4 == 3)
	{
		DebugBreak();
	}
	*/
    // if originator address is the last address in an entry in topology
    // table then return the last topology entry

    // RFC Section 9.5 Condition 2
    t_last = OlsrLookupLastTopologyTable(node, message->originator);

	/*
	if (node->nodeId == 1 && getSimTime(node) > 5)
	{

		DebugBreak();
	}
	*/


	if (SYMMETRIC_TOPOLOGY_TABLE)
	{

		clear_tco_node_addr_set(&(olsr->recent_delete_list));
		clear_tco_node_addr_set(&(olsr->recent_add_list));
	}

	olsr->naRecentChangedAddressByTC = GetIPv4Address(message->originator);

	/*
	if (node->nodeId == 1 && olsr->naRecentChangedAddressByTC == 12)
	{
		
		printf("OlsrProcessReceivedTc node->nodeId = %d, olsr->naRecentChangedAddressByTC = %d \n", node->nodeId, olsr->naRecentChangedAddressByTC);



		OlsrPrintTopologyTableSYM(node);

		//DebugBreak();
	}
	*/

	//printf("OlsrProcessReceivedTc begin \n");

    if (t_last != NULL)
    {
        if (DEBUG)
        {
            printf("T_Last exists in Topology table\n");
        }

        // current seq. is older than the last one, then message ignored
        if (SEQNO_GREATER_THAN(t_last->topology_seq, message->ansn))
        {
            OlsrDestroyTcMessage(message);

            if (DEBUG)
            {
                printf("TC_message too old\n");
            }



			//printf("OlsrProcessReceivedTc End A \n");

            return 1;
        }

        if (DEBUG)
        {
            printf("The new ANSN is %d and the old one is %d\n",
                message->ansn, t_last->topology_seq);
        }

        // Condition 3
        // For ANSN comparisons use section 19 of RFC
        // current seq. is newer than the last one

		// Peter Modified to test the function

		olsr->bDeleteOld = FALSE;
		olsr->bAddNew = FALSE;


        if (SEQNO_GREATER_THAN(message->ansn, t_last->topology_seq))
        {
            
			//Peter comment
			//figure out the least hop count for these entries to be deleted,
			//so as to avoid full route calculation

			//Peter added for supporting accumulative route calculation
			if (!SYMMETRIC_TOPOLOGY_TABLE)
			{
				olsr->changes_topology = TRUE;

				g_iTopologyChgByOlsrProcessReceivedTc++;				
			}
								
			// delete old entry from topology table
            OlsrDeleteLastTopolgyTable(t_last);


			BOOL bApplyForSymAsWell = TRUE;
			if (SYMMETRIC_TOPOLOGY_TABLE)
			{
				topology_last_entry * t_last_sym = OlsrLookupLastTopologyTableSYM(node, message->originator);
				if (t_last_sym != NULL)
				{
					
					/*
					if (node->nodeId == 15 && message->originator.interfaceAddr.ipv4 == 12)
					{
						DebugBreak();

						//printf("node->nodeId == 15 && message->originator.interfaceAddr.ipv4 == 12 \n");

					}
					*/
						
					if (OlsrDeleteLastTopolgyTableSYM(node, t_last_sym))
					{
						
					}
					else
					{
						bApplyForSymAsWell = FALSE;
					}
					
				}
				else
				{
					//this branch will never support to be called
					//printf("!!!!!!!!!!!! this branch should not exist because of the symmetric property in OlsrProcessReceivedTc 1 \n");
				}		

			}

            
            // We must insert new entries contained in received message
            t_last = (topology_last_entry *)
                    MEM_malloc(sizeof(topology_last_entry));

            memset(t_last, 0, sizeof(topology_last_entry));

            // Condition 4.1
            OlsrInsertLastTopologyTable(node, t_last, message, bApplyForSymAsWell);
            
			OlsrUpdateLastTable(node, t_last, message, addr_ip);
        }        
		else
        {

            // Condition 4.2
            // This the case where t_last->topology_seq == message->ansn, so
            // we must update the time out and create the new dest entries
			
			if (!SYMMETRIC_TOPOLOGY_TABLE)
			{
				//in fact, for this case, the topology will never change
				//or else the message->ansn != t_last->topology_seq

			}

			if (SYMMETRIC_TOPOLOGY_TABLE)
			{
				topology_last_entry * t_last_sym = OlsrLookupLastTopologyTableSYM(node, message->originator);
				if (t_last_sym == NULL)
				{
					//this branch will never support to be called
					//why
					
					//printf("!!!!!!!!!!!! this branch should not exist because of the symmetric property in OlsrProcessReceivedTc 3 \n");
					OlsrInsertLastTopologyTableSYM(node, message);
				}
			}
            	

            OlsrUpdateLastTable(node, t_last, message, addr_ip, TRUE);

			//assume it will not change the routing table ???
        }
		
    }
    else
    {

        // Condition 4.1
        // changes_topology will be set to DOWN  after recalculating the
        // routing table
        

		//Peter comment
		//figure out whether at least one entry of the mpr has already been in topology
		//if none of them already exist,then do full route calculation

		olsr->bDeleteOld = FALSE;
		olsr->bAddNew = FALSE;
		
        if (!SYMMETRIC_TOPOLOGY_TABLE)
		{
			olsr->changes_topology = TRUE;
				
			g_iTopologyChgByOlsrProcessReceivedTc++;
		}


        t_last = (topology_last_entry *)
                MEM_malloc(sizeof(topology_last_entry));

        memset(t_last, 0, sizeof(topology_last_entry));

		
		BOOL bApplyForSymAsWell = FALSE;
		
		if (SYMMETRIC_TOPOLOGY_TABLE)
		{
			bApplyForSymAsWell = TRUE;
			
			topology_last_entry * t_last_sym = OlsrLookupLastTopologyTableSYM(node, message->originator);
			if (t_last_sym != NULL)
			{
				
				bApplyForSymAsWell = FALSE;	
				//printf("!!!!!!!!!!!! this branch may exist because of the symmetric property in OlsrProcessReceivedTc 2 \n");			
			}
			else
			{
				
				//printf("!!!!!!!!!!!! this branch may exist because of the symmetric property in OlsrProcessReceivedTc 2 \n");
			}
		
			if (bApplyForSymAsWell)
			{

				insert_into_tco_node_addr_set(&(olsr->recent_add_list), GetIPv4Address(message->originator));
			}

		}

        OlsrInsertLastTopologyTable(node, t_last, message, bApplyForSymAsWell);

        OlsrUpdateLastTable(node, t_last, message, addr_ip);
    }

	BOOL bRTPrinted = FALSE;


	//
	//if (node->nodeId == 28 && dSimTime > 15.91 && dSimTime < 15.97 && source_addr.interfaceAddr.ipv4 == 34  && message->originator.interfaceAddr.ipv4 == 31)
	if (DEBUG)
	{
		g_iChaseRouteTable = 0;
		OlsrPrintTopologyTableSYM(node);
		g_iChaseRouteTable = 1;


		printf("================================================================\n\n");
	}

	char szTextRT[32768]; 

	

	
	int iRTAddOrDelete = 0;
	

	if (SYMMETRIC_TOPOLOGY_TABLE)
	{
		
		if (olsr->recent_add_list != NULL || olsr->recent_delete_list != NULL)
		{
			
			/*
			if (olsr->recent_add_list)
			{
				iRTAddOrDelete = iRTAddOrDelete + 1;
			}

			if (olsr->recent_delete_list)
			{
				iRTAddOrDelete = iRTAddOrDelete + 2;
			}

			*/

			
			
			if (node->nodeId == 76 && olsr->naRecentChangedAddressByTC == 39 && olsr->recent_add_list != NULL && olsr->recent_delete_list != NULL && dSimTime > 27.0 && dSimTime < 28.0)
			{

				//DebugBreak();
			}
			
			
			
			
			//if (iRTAddOrDelete == 2 && node->nodeId == 2 && olsr->naRecentChangedAddressByTC == 8 && olsr->recent_delete_list != NULL)
			//if (iRTAddOrDelete == 2)
			
			//if (olsr->recent_delete_list != NULL && node->nodeId == 8)
			//if (olsr->recent_delete_list != NULL)
			//if (g_iChaseRouteTable == 1 && node->nodeId == 30 && iRTAddOrDelete == 3 && olsr->naRecentChangedAddressByTC == 16)
			
			
			//if (FALSE)
			if (g_iChaseRouteTable == 1)
			{

				//DebugBreak();
				//printf("node->nodeId == 8 && iRTAddOrDelete == 2 && olsr->naRecentChangedAddressByTC == 10 %f \n", dSimTime);
				
				bRTPrinted = TRUE;

				memset(szTextRT, 0, 32768 * sizeof(char));
				PeterChaseTableChg(node, szTextRT, TRUE);
				//DebugBreak();
			}
			


			olsr->changes_topology = TRUE;

			g_iTopologyChgByOlsrProcessReceivedTc++;


			if (g_iAccumulativeRouteCalculation == 0)
			{

			}
			else if (g_iAccumulativeRouteCalculation == 1)
			{
			
				/*
				UInt16 uiMin = 10000;

				BOOL bExistCannotFound = FALSE;

				tco_node_addr * tco_add_list_tmp = olsr->recent_add_list;			
				while (tco_add_list_tmp != NULL)
				{

					Int16 iHopCnt = ProcessRoutingTableAccordingToTC(node, tco_add_list_tmp->nid, FALSE);

					if (iHopCnt == -1)
					{
						//can not find
						bExistCannotFound = TRUE;
					}
					else
					{

						uiMin = min(((int)uiMin), ((int)iHopCnt));
					}

					tco_add_list_tmp = tco_add_list_tmp->next;
				}


				tco_node_addr * tco_delete_list_tmp = olsr->recent_delete_list;
				while (tco_delete_list_tmp != NULL)
				{

					Int16 iHopCnt = ProcessRoutingTableAccordingToTC(node, tco_delete_list_tmp->nid, FALSE);

					if (iHopCnt == -1)
					{
						//can not find
						bExistCannotFound = TRUE;
					}
					else
					{

						uiMin = min(((int)uiMin), ((int)iHopCnt));
					}

					tco_delete_list_tmp = tco_delete_list_tmp->next;
				}


				if (uiMin != 10000)
				{

					olsr->uiConfidentCost = uiMin;
					if (olsr->uiConfidentCost > 1)
					{
						if (bExistCannotFound)
						{

							olsr->uiConfidentCost = max(olsr->uiConfidentCost - 3, 0);
						}
						else
						{

							olsr->uiConfidentCost = max(olsr->uiConfidentCost - 1, 0);
						}						
					}
					else
					{

						olsr->uiConfidentCost = 0;
					}
				}
				else
				{
					
					olsr->uiConfidentCost = 0;
				}

				//if (node->nodeId == 1)
				{
					printf("olsr->uiConfidentCost = %d \n", olsr->uiConfidentCost);
					printf("****************************************************************************************************** \n");
					printf("****************************************************************************************************** \n");
				}
				*/
			}
			else //g_iAccumulativeRouteCalculation == 2
			{
				
			}			
		}
	}


    // Call forwarding function here...
    OlsrForwardMessage(node,
        m,
        message->originator,
        message->packet_seq_number,
        incomingInterface,source_addr);

    OlsrDestroyTcMessage(message);

    if (DEBUG)
    {
        OlsrPrintTopologyTable(node);
    }


	if (FALSE)
	//if (bRTPrinted)
	{

		printf("Before OlsrProcessChanges for node %d, iRTAddOrDelete = %d \n", node->nodeId, iRTAddOrDelete);

		OlsrPrintRoutingTable(olsr->routingtable);
	}

    OlsrProcessChanges(node);



	if (SYMMETRIC_TOPOLOGY_TABLE)
	{

		clear_tco_node_addr_set(&(olsr->recent_delete_list));
		clear_tco_node_addr_set(&(olsr->recent_add_list));
	}


	//if(FALSE)
	if (bRTPrinted && g_iChaseRouteTable == 1)
	{

		PeterChaseTableChg(node, szTextRT, FALSE);

		
		//OlsrPrintRoutingTable(olsr->routingtable);

		//sprintf(szTextRT, "%s%s", szTextRT, g_szTextRT);


		


		
	}


	//printf("OlsrProcessReceivedTc End B \n");

    return 0;
}


/***************************************************************************
 *                  Definition of build and send message                   *
 ***************************************************************************/

// /**
// FUNCTION   :: OlsrBuildHelloPacket
// LAYER      :: APPLICATION
// PURPOSE    :: Build hello message
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + message: hl_message* : Pointer to hello msg structure
// + interfaceIndex: Int32: outgoing interface for hello pkt
// RETURN :: Int32 : 0
// **/

static
Int32 OlsrBuildHelloPacket(
    Node* node,
    hl_message* message,
    Int32 interfaceIndex)
{
    hello_neighbor* message_neighbor;
    hello_neighbor* tmp_neigh;
    link_entry* links;
    neighbor_entry* neighbor;
    neighborhash_type* hash_neighbor;

    unsigned char index;
    Int32 link;
    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;
    Address main_addr = olsr->main_address;

    Address outif_addr;


    if(olsr->ip_version == NETWORK_IPV6)
    {
        outif_addr.networkType = NETWORK_IPV6;
        Ipv6GetGlobalAggrAddress(
                node,
                interfaceIndex,
                &outif_addr.interfaceAddr.ipv6);
    }
    else if (olsr->ip_version == NETWORK_IPV4)
    {
        outif_addr.networkType = NETWORK_IPV4;
        outif_addr.interfaceAddr.ipv4 =
                        NetworkIpGetInterfaceAddress(node,interfaceIndex);
    }

    message->neighbors = NULL;
    message->packet_seq_number = 0;

    // message->mpr_seq_number = olsr->neighbortable.neighbor_mpr_seq;

    // Set Willingness
    message->willingness = olsr->willingness;
    message->ttl = 1;
    message->source_addr = main_addr;

    links = olsr->link_set;

    while (links != NULL)
    {
        link = OlsrLookupLinkStatus(node, links);

        if (!Address_IsSameAddress(&(links->local_iface_addr), &outif_addr))
        {
            links = links->next;
            continue;
        }

        if (DEBUG)
        {
            printf (" Node %d: Adding neighbors in hello \n", node->nodeId);
            char addrString1[MAX_STRING_LENGTH];
            char addrString2[MAX_STRING_LENGTH];
            IO_ConvertIpAddressToString(&links->neighbor_iface_addr,
                                        addrString1);
            IO_ConvertIpAddressToString(&links->local_iface_addr,
                                        addrString2);
            printf(" Neighbor iface addr : %s  Local Iface Addr: %s \n",
                addrString1, addrString2);
        }

        message_neighbor = (hello_neighbor *)
                    MEM_malloc(sizeof(hello_neighbor));

        memset(message_neighbor, 0, sizeof(hello_neighbor));

        message_neighbor->link = (unsigned char)link;

        if (links->neighbor->neighbor_is_mpr)
        {
            message_neighbor->status = MPR_NEIGH;
        }
        else
        {
            if (links->neighbor->neighbor_status == SYM)
            {
                message_neighbor->status = SYM_NEIGH;
            }
            else if (links->neighbor->neighbor_status == NOT_SYM)
            {
                message_neighbor->status = NOT_NEIGH;
            }
        }

        message_neighbor->address = links->neighbor_iface_addr;
        message_neighbor->main_address = links->neighbor->neighbor_main_addr;
        message_neighbor->next = message->neighbors;
        message->neighbors = message_neighbor;

        links = links->next;
    }

    // If Multiple OLSR interfaces

    if (olsr->numOlsrInterfaces > 1)
    {
        for (index = 0; index < HASHSIZE; index++)
        {
            hash_neighbor = &olsr->neighbortable.neighborhash[index];

            for (neighbor = hash_neighbor->neighbor_forw;
                    neighbor!= (neighbor_entry *) hash_neighbor;
                    neighbor = neighbor->neighbor_forw)
            {
                tmp_neigh = message->neighbors;

                while (tmp_neigh)
                {
                    if (Address_IsSameAddress(&tmp_neigh->main_address,
                            &neighbor->neighbor_main_addr))
                    {
                        break;
                    }
                    tmp_neigh = tmp_neigh->next;
                }

                if (tmp_neigh)
                {
                    continue;
                }

                message_neighbor = (hello_neighbor *)
                    MEM_malloc(sizeof(hello_neighbor));

                memset(message_neighbor, 0, sizeof(hello_neighbor));

                message_neighbor->link = UNSPEC_LINK;

                if (neighbor->neighbor_is_mpr)
                {
                    message_neighbor->status = MPR_NEIGH;
                }
                else
                {
                    if(neighbor->neighbor_status == SYM)
                    {
                        message_neighbor->status = SYM_NEIGH;
                    }

                    else if (neighbor->neighbor_status == NOT_SYM)
                    {
                        message_neighbor->status= NOT_NEIGH;
                    }

                }

                message_neighbor->address = neighbor->neighbor_main_addr;
                message_neighbor->main_address = neighbor->neighbor_main_addr;

                message_neighbor->next = message->neighbors;
                message->neighbors = message_neighbor;
            }
        }
    }

    return 0;
}


// /**
// FUNCTION   :: OlsrGenerateHello
// LAYER      :: APPLICATION
// PURPOSE    :: Generate hello message
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + interfaceIndex: Int32: interface for which msg is to be
//                        generated
// RETURN :: void : NULL
// **/

static
void OlsrGenerateHello(
    Node* node,
    Int32 interfaceIndex)
{
    hl_message hellopacket;

    // receive hello packet info from the node structure to hl_message
    OlsrBuildHelloPacket(node, &hellopacket, interfaceIndex);

    // prepare the hello message and send
    OlsrSendHello(node, &hellopacket, interfaceIndex);

}

// /**
// FUNCTION   :: RoutingOlsrHandlePacket
// LAYER      :: APPLICATION
// PURPOSE    :: Handles OLSR control message received from transport layer
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + msg : Message* : Pointer to Message
// RETURN :: void : NULL
// **/

static
void RoutingOlsrHandlePacket(
    Node* node,
    Message* msg)
{
    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    //NON-OLSR node received OLSR packet
    if (olsr == NULL)
    {
        return;
    }
    olsrpacket* olsr_pkt = (olsrpacket *) MESSAGE_ReturnPacket(msg);

    // set m pointer to first msg
    olsrmsg* m = olsr_pkt->olsr_msg;

    Int32 size;
    Int32 msgsize;
    Int32 count;
    Int32 minsize = (sizeof(unsigned char) * 4);

    hl_message hellopacket;
    tc_message tcpacket_in;
    mid_message midpacket_in;
    hna_message hnapacket_in;

     ActionData acnData;
     acnData.actionType = RECV;
     acnData.actionComment = NO_COMMENT;
     TRACE_PrintTrace(node,
                      msg,
                      TRACE_APPLICATION_LAYER,
                      PACKET_IN,
                      &acnData);

    UdpToAppRecv* udpToApp = (UdpToAppRecv *) MESSAGE_ReturnInfo(msg);

    // sender address received from info field
    Address source_addr = udpToApp->sourceAddr;

    // incoming interface received from info field
    Int32 incomingInterface = udpToApp->incomingInterfaceIndex;

    // check whether message is for OLSR only
    if (NetworkIpGetUnicastRoutingProtocolType(node,
        incomingInterface, olsr->ip_version) != ROUTING_PROTOCOL_OLSR_INRIA)
    {
        return;
    }

    // Get main address (address of default interface)
    Address main_addr = olsr->main_address;

    Address originator_address;


    // New RFC version support for multiple messages in OLSR packet

    // First get the size of the packet

    // Get the size of the message portion by subtracting the packet size and
    // the size of the olsr packet header, verify this with the olsr packet
    // size in the packet header

    // Process each message portion by shifting the message pointer to the
    // next message once the message is processed

    // For unknown type, discard message for now

    // Get packet size
    size = MESSAGE_ReturnPacketSize(msg);

    // Get message portion size of the packet as count
    count = olsr_pkt->olsr_packlen - minsize;

    if (DEBUG)
    {
        printf("\nNode %d  Receiving a packet: Size of messages in packet is %d\n",node->nodeId, count);
    }

    // RFC Section 3.4 Condition 1

    if (count < minsize)
    {
        return;
    }

    while (count > 0)
    {
        if(count < minsize)
        {
            break;
        }

        unsigned char ttl;

        if (olsr->ip_version == NETWORK_IPV6)
        {
            ttl = m->olsr_msg_tail.olsr_ipv6_msg.ttl;
        }
        else

        {
            ttl = m->olsr_msg_tail.olsr_ipv4_msg.ttl;
        }
        // RFC 3626 Section 3.4 Condition 2
        if (ttl <= 0)
        {
            if (DEBUG)
            {
                printf("Dropping message type %d from neigh with TTL 0\n",
                                                         m->olsr_msgtype);
            }

            count = count - m->olsr_msg_size;
            continue;
        }

        if (olsr->ip_version == NETWORK_IPV6)
        {

            SetIPv6AddressInfo(&originator_address,
                                m->originator_ipv6_address);
        }
        else

        {
            SetIPv4AddressInfo(&originator_address,
                               m->originator_ipv4_address);
        }
        if (Address_IsSameAddress(&main_addr, &originator_address))
        {
            if (DEBUG)
            {
                printf("Not processing message originating from us \n");
            }
            count = count - m->olsr_msg_size;
            continue;
        }

        // RFC 3626 Section 3.4 Condition 3 seems  relevant for only TC and Mid message types
        // olsrd implem/geentation includes it only for TC messages and mid
        // messages
        // RFC 3626 Section 3.4 Condition 4 seems only relevant for TC, MID
        // messages and unknown types, We discard unknown types currently and
        // implement condition 4 in TC and mid message processing similar to olsrd
        // implementation

        switch (m->olsr_msgtype)
        {

            case HELLO_PACKET:
            {
                // hello message received, convert it to hl_message structure
                OlsrHelloChgeStruct(node, &hellopacket, m);

                // process hello message
                OlsrProcessReceivedHello(node,
                    &hellopacket,
                    incomingInterface,
                    source_addr);
                break;
            }
            case TC_PACKET:
            {

                // tc message received, convert it to tc_message structure
                OlsrTcChgeStruct( node, &tcpacket_in, m, source_addr);

                // process tc message
                OlsrProcessReceivedTc(node,
                    &tcpacket_in,
                    source_addr,
                    incomingInterface,
                    m);

                break;
            }
            case MID_PACKET:
            {
                // mid message received, convert it to mid_message structure
                OlsrMidChgeStruct(node, &midpacket_in, m);

                // process mid message
                OlsrProcessReceivedMid(node,
                    &midpacket_in,
                    source_addr,
                    incomingInterface,
                    m);

                break;
            }
            case HNA_PACKET:
            {
                // mid message received, convert it to mid_message structure
                OlsrHnaChgeStruct(node, &hnapacket_in, m);

                // process mid message
                OlsrProcessReceivedHna(node,
                    &hnapacket_in,
                    source_addr,
                    incomingInterface,
                    m);

                break;
            }


            default:
            {
                if (DEBUG)
                {
                    printf("Unknown OLSR message type\n");
                }
                // Ideally forward this message if originator node is not me
                UInt16 seqno;

                if (olsr->ip_version == NETWORK_IPV6)
                {
                    seqno = m->olsr_msg_tail.olsr_ipv6_msg.msg_seq_no;
                }
                else

                {
                    seqno = m->olsr_msg_tail.olsr_ipv4_msg.msg_seq_no;
                }


                OlsrForwardMessage(
                    node,
                    m,
                    originator_address,
                    seqno,
                    incomingInterface,
                    source_addr);

                break;

            }

        } // end switch

        msgsize = m->olsr_msg_size;

        if (DEBUG)
        {
            printf (" Node %d: size of this message is %d\n",
                node->nodeId, msgsize);
        }

        count = count - msgsize;

        if (count < 0)
        {
            if (DEBUG)
            {
                printf(" Error in packet length\n");
            }
            break;
        }

        // Move the message pointer  to the next message
        m = (olsrmsg *) ((char *)m + msgsize);

    } // end while

} // end function


// /**
// FUNCTION   :: OlsrPrintTraceXML
// LAYER      :: NETWORK
// PURPOSE    :: Print LSA header trace information in XML format
// PARAMETERS ::
// + node : Node* : Pointer to node, doing the packet trace
// + msg  : Message* : Pointer to Message
// RETURN ::  void : NULL
// **/

void OlsrPrintTraceXML(
       Node* node,
       Message* msg)
{
    char buf[MAX_STRING_LENGTH];
    char origAddr[MAX_STRING_LENGTH];
    char neigAddr[MAX_STRING_LENGTH];

    Int32 size;
    Int32 msgsize;
    Int32 count;
    Int32 minsize = (sizeof(unsigned char) * 4);
    Float32 vtime;

    unsigned char ttl;
    unsigned char hopCount;
    UInt16 msgSeqNo;

    olsrpacket* olsr_pkt = (olsrpacket *) MESSAGE_ReturnPacket(msg);

    // set m pointer to first msg
    olsrmsg* m = (olsrmsg* )olsr_pkt->olsr_msg;

    // Get olsr node pointer
    RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

    // Get main address (address of default interface)
    Address source_addr = MAPPING_GetDefaultInterfaceAddressInfoFromNodeId(
                                       node,
                                       msg->originatingNodeId,
                                       olsr->ip_version);

    sprintf(buf, "<olsr>");
    TRACE_WriteToBufferXML(node, buf);

    sprintf(buf, "%hu %hu ",
        olsr_pkt->olsr_packlen,
        olsr_pkt->olsr_pack_seq_no);
     TRACE_WriteToBufferXML(node, buf);

     // Get packet size
    size = MESSAGE_ReturnPacketSize(msg);

    // Get size of the message in packet as count
    count = olsr_pkt->olsr_packlen - minsize;

    if (count < minsize)
    {
        return;
    }

    sprintf(buf, " <olsrMsgList>");
    TRACE_WriteToBufferXML(node, buf);

    while (count > 0)
    {

        if(count < minsize)
        {
            break;
        }

        if (olsr->ip_version == NETWORK_IPV6)
        {

            ttl = m->olsr_msg_tail.olsr_ipv6_msg.ttl;
            hopCount = m->olsr_msg_tail.olsr_ipv6_msg.hop_count;
            msgSeqNo = m->olsr_msg_tail.olsr_ipv6_msg.msg_seq_no;
            IO_ConvertIpAddressToString(&m->originator_ipv6_address,
                                        origAddr);

        }
        else
        {
              ttl = m->olsr_msg_tail.olsr_ipv4_msg.ttl;
              hopCount = m->olsr_msg_tail.olsr_ipv4_msg.hop_count;
              msgSeqNo = m->olsr_msg_tail.olsr_ipv4_msg.msg_seq_no;
              IO_ConvertIpAddressToString(m->originator_ipv4_address,
                                          origAddr);
        }

       vtime = OlsrME2Double(m->olsr_vtime);

       sprintf(buf, "%hu %f %hu %s %hu %hu %hu ",
                        m->olsr_msgtype,
                        vtime,
                        m->olsr_msg_size,
                        origAddr,
                        ttl,
                        hopCount,
                        msgSeqNo);
                        TRACE_WriteToBufferXML(node, buf);

        switch (m->olsr_msgtype)
        {
        case HELLO_PACKET:
            {

                char neighborAddr[MAX_STRING_LENGTH];
                in6_addr* h_ipv6_addr = NULL;
                NodeAddress* h_ipv4_addr = NULL;
                NodeAddress* h_ipv4_adr;
                in6_addr* h_ipv6_adr;
                hl_message hellopacket;
                hellomsg* h;
                hellinfo* hinfo;
                hellinfo* hinf;
                hello_neighbor* neighbors;

                // hello message received, convert it to hl_message structure
                OlsrHelloChgeStruct(node, &hellopacket, m);

                if (olsr->ip_version == NETWORK_IPV6)
                {
                    h = m->olsr_ipv6_hello;
                    hinfo = h->hell_info;
                    IO_ConvertIpAddressToString(
                        &hinfo->neigh_addr->ipv6_addr,
                        neigAddr);
                }
                else

                {
                    h = m->olsr_ipv4_hello;
                    hinfo = h->hell_info;
                    IO_ConvertIpAddressToString(
                        hinfo->neigh_addr->ipv4_addr,
                        neigAddr);
                }

                sprintf(buf, " <helloMsg>");
                TRACE_WriteToBufferXML(node, buf);

               sprintf(buf, "%hu %f %hu ",
                   0,//reserved
                   OlsrME2Double(h->htime),
                   h->willingness);
               TRACE_WriteToBufferXML(node, buf);



               sprintf(buf, "<linkInfolist>");
               TRACE_WriteToBufferXML(node, buf);

                for (hinf = hinfo;
                     (char *)hinf < (char *)m + m->olsr_msg_size;
                     hinf = (hellinfo *)((char *)hinf +
                                            hinf->link_msg_size))
                {

                     if (olsr->ip_version == NETWORK_IPV6)
                     {

                        h_ipv6_addr = (in6_addr *)hinf->neigh_addr;
                        h_ipv6_adr = h_ipv6_addr;

                         while ((char *)h_ipv6_adr < (char *)hinf +
                                                        hinf->link_msg_size)
                         {

                            char neighborAddr[MAX_STRING_LENGTH];
                            IO_ConvertIpAddressToString(
                                                &hinf->neigh_addr->ipv6_addr,
                                                neighborAddr);

                            sprintf(buf,
                                    "<helloInfo>%hu %hu %hu %s </helloInfo>",
                                        EXTRACT_LINK(hinf->link_code),
                                        0,//reserved
                                        hinf->link_msg_size,
                                        neigAddr);
                            TRACE_WriteToBufferXML(node, buf);
                             h_ipv6_adr++;
                        }

                    }
                    else
                    {

                            h_ipv4_addr = (NodeAddress *)hinf->neigh_addr;
                            h_ipv4_adr = h_ipv4_addr;

                            while ((char *)h_ipv4_adr < (char *)hinf +
                                                        hinf->link_msg_size)
                            {

                                char addrString[MAX_STRING_LENGTH];
                                IO_ConvertIpAddressToString(*h_ipv4_adr,
                                                              addrString);

                                sprintf(buf,
                                "<helloInfo>%hu %hu %hu %s </helloInfo>",
                                                   EXTRACT_LINK(hinf->link_code),
                                                   0,//reserved
                                                   hinf->link_msg_size,
                                                   addrString);
                                TRACE_WriteToBufferXML(node, buf);
                                h_ipv4_adr++;

                        }

                    }//end of else
                }//end of for loop

               sprintf(buf, "</linkInfolist>");
               TRACE_WriteToBufferXML(node, buf);

               sprintf(buf, "<neighbourList>");
               TRACE_WriteToBufferXML(node, buf);

               IO_ConvertIpAddressToString(&hellopacket.source_addr,
                       neighborAddr);
               neighbors = hellopacket.neighbors;

               while (neighbors != NULL)
               {
                    IO_ConvertIpAddressToString(&neighbors->address,
                                                neighborAddr);
                    sprintf(buf, "<neighbours>%s </neighbours>",
                            neighborAddr);

                    TRACE_WriteToBufferXML(node, buf);
                    neighbors = neighbors->next;
                }//end of while
               sprintf(buf, " </neighbourList>");
               TRACE_WriteToBufferXML(node, buf);

               sprintf(buf, " </helloMsg>");
               TRACE_WriteToBufferXML(node, buf);
               OlsrDestroyHelloMessage(&hellopacket);
               break;
            }//end hello packet case
        case TC_PACKET:
            {
                NodeAddress* mprs_ipv4_addr = NULL;
                in6_addr* mprs_ipv6_addr = NULL;
                tcmsg* tc = NULL;
                tc_message message;
                tc_mpr_addr* mprs;

                char addrString1[MAX_STRING_LENGTH];
                char addrString2[MAX_STRING_LENGTH];

                // tc message received, convert it to tc_message structure
                OlsrTcChgeStruct( node, &message, m, source_addr);

                if (olsr->ip_version == NETWORK_IPV6)
                {
                    tc = m->olsr_ipv6_tc;
                    mprs_ipv6_addr =
                        (in6_addr *)tc->adv_neighbor_main_address;
                }
                else
                {
                    tc = m->olsr_ipv4_tc;
                    mprs_ipv4_addr =
                        (NodeAddress *)tc->adv_neighbor_main_address;
                }

                IO_ConvertIpAddressToString(&message.source_addr,
                                            addrString1);

                 IO_ConvertIpAddressToString(&message.originator,
                                             addrString2);

                mprs = message.multipoint_relay_selector_address;

                sprintf(buf, "<tcMsg>");
                TRACE_WriteToBufferXML(node, buf);

                sprintf(buf, "%s %s %hu %hu %hu ",
                         addrString1,
                         addrString2,
                         message.packet_seq_number,
                         message.hop_count,
                         message.ansn);

                TRACE_WriteToBufferXML(node, buf);

                sprintf(buf, " <mprsAddrlist>");
                TRACE_WriteToBufferXML(node, buf);

                while (mprs != NULL)
                {
                    sprintf(buf, " <mprsAddr>");
                    TRACE_WriteToBufferXML(node, buf);

                    IO_ConvertIpAddressToString(&mprs->address,
                                                addrString1);

                    sprintf(buf, "%s ",
                        addrString1);
                    TRACE_WriteToBufferXML(node, buf);

                    mprs = mprs->next;

                   sprintf(buf, " </mprsAddr>");
                   TRACE_WriteToBufferXML(node, buf);
                }

                sprintf(buf, " </mprsAddrlist>");
                TRACE_WriteToBufferXML(node, buf);

                sprintf(buf, " </tcMsg>");
                TRACE_WriteToBufferXML(node, buf);
                OlsrDestroyTcMessage(&message);
                break;
            }//end of TC packet case
       case MID_PACKET :
            {
                char addrString[MAX_STRING_LENGTH];
                char addrString1[MAX_STRING_LENGTH];
                mid_message midpacket;
                midmsg* mid_msg = NULL;
                NodeAddress* alias_ipv4_addr = NULL;
                in6_addr* alias_ipv6_addr = NULL;
                mid_alias* mid_addr;
                Float32 vtime;

                sprintf(buf, "<midPacket>");
                TRACE_WriteToBufferXML(node, buf);

                // receive mid packet info from the node structure to
                // mid_message
                // mid message received, convert it to mid_message structure

                OlsrMidChgeStruct(node, &midpacket, m);

                if (olsr->ip_version == NETWORK_IPV6)
                {
                    mid_msg = m->olsr_ipv6_mid;
                    alias_ipv6_addr = (in6_addr *)mid_msg->olsr_iface_addr;
                }
                else

                {
                    mid_msg = m->olsr_ipv4_mid;
                    alias_ipv4_addr =
                        (NodeAddress *)mid_msg->olsr_iface_addr;
                }

                IO_ConvertIpAddressToString(&midpacket.mid_origaddr,
                                    addrString);

                IO_ConvertIpAddressToString(&midpacket.main_addr,
                                             addrString1);
                vtime = OlsrME2Double((unsigned char) midpacket.vtime);

                 sprintf(buf, "%f %s %hu %hu %hu %s ",
                     vtime,
                     addrString,
                     midpacket.mid_hopcnt,
                     midpacket.mid_ttl,
                     midpacket.mid_seqno,
                     addrString1);

                TRACE_WriteToBufferXML(node, buf);


               sprintf(buf, "<midaliaslist>");
               TRACE_WriteToBufferXML(node, buf);

                mid_addr = midpacket.mid_addr;

                while (mid_addr != NULL)
                {
                    sprintf(buf, "<midAddr>");
                    TRACE_WriteToBufferXML(node, buf);

                    IO_ConvertIpAddressToString(&mid_addr->alias_addr,
                        addrString);

                    sprintf(buf, "%s ",
                        addrString);
                    TRACE_WriteToBufferXML(node, buf);

                    mid_addr = mid_addr->next;

                    sprintf(buf, "</midAddr>");
                    TRACE_WriteToBufferXML(node, buf);
                }//end of while

                sprintf(buf, "</midaliaslist>");
                TRACE_WriteToBufferXML(node, buf);

                sprintf(buf, " </midPacket>");
                TRACE_WriteToBufferXML(node, buf);
                OlsrDestroyMidMessage(&midpacket);

               break;
            }//end of mid packet case
       case HNA_PACKET :
           {
                char originatorAddr[MAX_STRING_LENGTH];

                char addrString1[MAX_STRING_LENGTH];
                hna_message hnapacket;
                hnamsg* hna_msg = NULL;
                struct _hnapair_ipv6* hnapair_ipv6 = NULL;
                struct _hnapair_ipv4* hnapair_ipv4 = NULL;
                Float32 vtime;
                UInt16 netPrefixlength;

                sprintf(buf, " <hnaPacket>");
                TRACE_WriteToBufferXML(node, buf);

                //hna message received, convert it to hna_message structure
                OlsrHnaChgeStruct(node, &hnapacket, m);

                if (olsr->ip_version == NETWORK_IPV6)
                {
                    hna_msg = m->olsr_ipv6_hna;
                    hnapair_ipv6 =
                        (struct _hnapair_ipv6* )hna_msg->hna_net_pair;
                }
                else

                {
                    hna_msg = m->olsr_ipv4_hna;
                    hnapair_ipv4 =
                        (struct _hnapair_ipv4* )hna_msg->hna_net_pair;
                }
                vtime = OlsrME2Double((unsigned char) hnapacket.vtime); // validity time
                IO_ConvertIpAddressToString(&hnapacket.hna_origaddr,
                                            originatorAddr);

                sprintf(buf, "%f %s %hu %hu %hu ",
                     vtime,
                     originatorAddr,
                     hnapacket.hna_seqno,
                     hnapacket.hna_hopcnt,
                     hnapacket.hna_ttl
                     );

                TRACE_WriteToBufferXML(node, buf);

                hna_net_addr* hna_net_pair = hnapacket.hna_net_pair;

                sprintf(buf, " <hnanetPairList>");
                TRACE_WriteToBufferXML(node, buf);

                while (hna_net_pair != NULL)
                {
                    char addrString[MAX_STRING_LENGTH];

                    IO_ConvertIpAddressToString(&hna_net_pair->net,
                                                addrString);

                    if (olsr->ip_version == NETWORK_IPV6)
                    {
                        netPrefixlength = (UInt16)hna_net_pair->netmask.v6;

                        sprintf(buf, "<hnanetPairv6>%s %hu </hnanetPairv6>",
                                    addrString,
                                    netPrefixlength);
                        TRACE_WriteToBufferXML(node, buf);

                    }
                    else
                    {
                         IO_ConvertIpAddressToString(
                                                   hna_net_pair->netmask.v4,
                                                   addrString1);

                          sprintf(buf, "<hnanetPairv4>%s %s </hnanetPairv4>",
                                    addrString,
                                    addrString1);
                            TRACE_WriteToBufferXML(node, buf);

                    }

                    hna_net_pair = hna_net_pair->next;
                }

                sprintf(buf, " </hnanetPairList>");
                TRACE_WriteToBufferXML(node, buf);

                sprintf(buf, " </hnaPacket>");
                TRACE_WriteToBufferXML(node, buf);

                OlsrDestroyHnaMessage(&hnapacket);

                break;
           }//end of hna packet case

       }//end of switch
        msgsize = m->olsr_msg_size;
        count = count - msgsize;
        // Move the message pointer  to the next message
        m = (olsrmsg *) ((char *)m + msgsize);


    }//end of while loop count>0

    sprintf(buf, "</olsrMsgList>");
    TRACE_WriteToBufferXML(node, buf);

    sprintf(buf, "</olsr>");
    TRACE_WriteToBufferXML(node, buf);

}

// /**
// FUNCTION   :: OlsrInitTrace
// LAYER      :: APPLCATION
// PURPOSE    :: Olsr initialization  for tracing
// PARAMETERS ::
// + node : Node* : Pointer to node
// + nodeInput    : const NodeInput* : Pointer to NodeInput
// RETURN ::  void : NULL
// **/

static
void OlsrInitTrace(Node* node, const NodeInput* nodeInput)
{

	//Peter Added for test

	

	if (g_iNeighborChangeCnt == -1 && g_iTopologyChangeCnt == -1 && g_iBothChg == -1)
	{

		g_iNeighborChangeCnt = 0;
		g_iTopologyChangeCnt = 0;
		g_iBothChg = 0;

		g_iNeighborChgByOlsrInsertMidAlias = 0;
		//g_iNeighborChgByOlsrUpdateNeighborStatus = 0;
		g_iNeighborChgByOlsrTimeoutLinkEntry = 0;
		g_iNeighborChgByOlsrTimeout2HopNeighbors = 0;
		g_iNeighborChgByOlsrProcessNeighborsInHelloMsg = 0;
		g_iNeighborChgByOlsrProcessReceivedHello = 0;



		g_iTopologyChgByOlsrInsertMidAlias = 0;
		g_iTopologyChgByOlsrUpdateHnaEntry = 0;
		//g_iTopologyChgByOlsrUpdateNeighborStatus = 0;
		g_iTopologyChgByOlsrTimeout2HopNeighbors = 0;
		g_iTopologyChgByOlsrUpdateLastTable = 0;
		g_iTopologyChgByOlsrTimeoutTopologyTable = 0;
		g_iTopologyChgByOlsrProcessNeighborsInHelloMsg = 0;
		g_iTopologyChgByOlsrProcessReceivedHello = 0;
		g_iTopologyChgByOlsrProcessReceivedMid = 0;
		g_iTopologyChgByOlsrProcessReceivedTc = 0;

		g_iTopologyChgByOlsrProcessReceivedTcAddNew = 0;
		g_iTopologyChgByOlsrProcessReceivedTcDeleteOld = 0;

		g_iTopologyChgApplyARC = 0;

		g_iNeighborhoodChgApplyARC = 0;

		g_iTopologyChgApplyNormal = 0;



		g_iTopologyChgApplyARC_With_Delete = 0;	
		g_iTopologyChgApplyARC_With_Delete_Success = 0;
		g_iTopologyChgApplyARC_With_Delete_Failed_Cause_Rediscovery = 0;
	

	}




    char buf[MAX_STRING_LENGTH];
    BOOL retVal;
    BOOL traceAll = TRACE_IsTraceAll(node);
    BOOL trace = FALSE;
    static BOOL writeMap = TRUE;

    IO_ReadString(
        node->nodeId,
        ANY_ADDRESS,
        nodeInput,
        "TRACE-OLSR",
        &retVal,
        buf);

    if (retVal)
    {
        if (strcmp(buf, "YES") == 0)
        {
            trace = TRUE;
        }
        else if (strcmp(buf, "NO") == 0)
        {
            trace = FALSE;
        }
        else
        {
            ERROR_ReportError(
                "TRACE-OLSR should be either \"YES\" or \"NO\".\n");
        }
    }
    else
    {
        if (traceAll)
        {
            trace = TRUE;
        }
    }

    if (trace)
    {
            TRACE_EnableTraceXML(node, TRACE_OLSR,
                "OSLR", OlsrPrintTraceXML, writeMap);
    }
    else
    {
           TRACE_DisableTraceXML(node, TRACE_OLSR,
               "OLSR", writeMap);
    }

	if (OLSR_FORWARDIND_PATH_DEBUG_TRACE)
	{
		// Empty or create a file named aodv.trace to print the packet
		// contents
		
		if (g_szOutputRouteChaseFileName != NULL && 0 != strlen(g_szOutputRouteChaseFileName))
		{


			FILE* fp_trace = fopen(g_szOutputRouteChaseFileName, "w");
			fclose(fp_trace);
		}
		
		
		FILE* fp = fopen("olsr_routing_path.trace", "w");
		fclose(fp);

	}

	if (_TEST_TIME_COMPLEXITY || FORWARD_WITH_PURE_ROUTE_TABLE)
	{

		if (g_szRoot == NULL)
		{

			g_szRoot = new char[MAX_PATH];
			ZeroMemory(g_szRoot, MAX_PATH * sizeof(char));


			FILE* fpi = fopen("olsrTC.file", "r");
			if (!fpi) 
			{

			}
			else
			{
				
				char sLine[MAX_PATH] = {0};

				char sEqualSign[MAX_PATH] = {0};
				char sTmp[MAX_PATH] = {0};

				char szMatchSTART_NODE_ID[MAX_PATH] = "START_NODE_ID";
				char szMatchEND_NODE_ID[MAX_PATH] = "END_NODE_ID";
				char szMatchROOT[MAX_PATH] = "ROOT";
					
				char szMatchSpeed[MAX_PATH] = "SPEED";

				while(!feof(fpi))
				{ 

					ZeroMemory(sLine, MAX_PATH * sizeof(char));

					fgets(sLine, MAX_PATH, fpi);

					ZeroMemory(sTmp, MAX_PATH * sizeof(char));
					ZeroMemory(sEqualSign, MAX_PATH * sizeof(char));

				
					if (0 == strncmp(sLine, szMatchSTART_NODE_ID, strlen(szMatchSTART_NODE_ID)))
					{
						sscanf(sLine + strlen(szMatchSTART_NODE_ID), "%s %s", sEqualSign, sTmp);

						NODE_ID_FOR_TEST_START = atoi(sTmp);

					}
					else if (0 == strncmp(sLine, szMatchEND_NODE_ID, strlen(szMatchEND_NODE_ID)))
					{
						sscanf(sLine + strlen(szMatchEND_NODE_ID), "%s %s", sEqualSign, sTmp);

						NODE_ID_FOR_TEST_END = atoi(sTmp);
					}
					else if (0 == strncmp(sLine, szMatchROOT, strlen(szMatchROOT)))
					{
						sscanf(sLine + strlen(szMatchROOT), "%s %s", sEqualSign, g_szRoot);
						
					}
		                        else if (0 == strncmp(sLine, szMatchSpeed, strlen(szMatchSpeed)))
					{
						sscanf(sLine + strlen(szMatchSpeed), "%s %s", sEqualSign, sTmp);

						g_iMobilitySpeed = (int)atoi(sTmp);
					}

				}		

				if (fpi) 
				{

					fclose(fpi);
				}



			}


			char sTmp[MAX_PATH] = {0};
			ZeroMemory(sTmp, MAX_PATH * sizeof(char));

                        sprintf(sTmp, "Speed-%d", g_iMobilitySpeed);

			if (_OLSR_MULTIPATH)
			{

				sprintf(sTmp, "%s-%s-EstimateTimeComplexity_MP", sTmp, g_szRoot);

			}
			else
			{

				sprintf(sTmp, "%s-%s-EstimateTimeComplexity_SP", sTmp, g_szRoot);

			}

			

			sprintf(sTmp, "%s_ARC_%d_%d", sTmp, g_iAccumulativeRouteCalculation, g_iToAchieveSameRoute);

			FILE* fp_time_complexity = fopen(sTmp, "w");
			fclose(fp_time_complexity);


		}

	}

	

    writeMap = FALSE;
}

// /**
// FUNCTION   :: RoutingOlsrInriaInit
// LAYER      :: APPLICATION
// PURPOSE    :: Initialization function for OLSR.
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + nodeInput : const NodeInput* : Pointer to input configuration
// + interfaceIndex: Int32: Interface being initialized
// RETURN :: void : NULL
// **/

void RoutingOlsrInriaInit(
    Node *node,
    const NodeInput* nodeInput,
    Int32 interfaceIndex,
    NetworkType networkType)
{

	//Peter added for support trace
   	
	/*
	if (_TEST_TIME_COMPLEXITY && g_strTxt == NULL)
	{

		g_strTxt = new char[File_Buf_Size];
		memset(g_strTxt, 0, File_Buf_Size * sizeof(char));
	}
	*/
	
	
	RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;
    unsigned char index;
    char errStr[MAX_STRING_LENGTH];

    if (olsr == NULL)
    {

        // Allocate Olsr struct
        olsr = (RoutingOlsr* ) MEM_malloc(sizeof(RoutingOlsr));

        memset(olsr, 0, sizeof(RoutingOlsr));

        node->appData.olsr = (void *) olsr;


		//Peter added for support route cache
		ZeroMemory(&olsr->rci, sizeof(RouteCacheItem));




        // initialize sequence number
        olsr->numOlsrInterfaces = 1;
        olsr->mpr_coverage = 1;
        olsr->willingness = WILL_DEFAULT;

        /* initialize random seed */
        RANDOM_SetSeed(olsr->seed,
                       node->globalSeed,
                       node->nodeId,
                       APP_ROUTING_OLSR_INRIA);

        olsr->message_seqno = 1;
        olsr->tcMessageStarted = FALSE;

        // initialize stat variables
        olsr->olsrStat.numHelloReceived = 0;
        olsr->olsrStat.numHelloSent = 0;
        olsr->olsrStat.numTcReceived = 0;
        olsr->olsrStat.numTcGenerated = 0;
        olsr->olsrStat.numTcRelayed = 0;
        olsr->olsrStat.numMidReceived = 0;
        olsr->olsrStat.numMidGenerated = 0;
        olsr->olsrStat.numMidRelayed = 0;
        olsr->olsrStat.numHnaReceived = 0;
        olsr->olsrStat.numHnaGenerated = 0;
        olsr->olsrStat.numHnaRelayed = 0;
        olsr->statsPrinted = FALSE;



		if (g_iRunTimeCompare == 1)
		{
						
			olsr->pszInfo = new char[INFO_SIZE];
			
			olsr->pszOrigRT = new char[RT_SIZE];
			olsr->pszMiddleRT = new char[RT_SIZE];
			olsr->pszRTWithARC = new char[RT_SIZE];
			olsr->pszRTWithoutARC = new char[RT_SIZE];

			olsr->pszOtherTables = new char[RT_SIZE];
		}
		else
		{
			olsr->pszInfo = NULL;

			olsr->pszOrigRT = NULL;
			olsr->pszMiddleRT = NULL;
			olsr->pszRTWithARC = NULL;
			olsr->pszRTWithoutARC = NULL;

			olsr->pszOtherTables = NULL;
		}


		olsr->dRCRealRuntime = 0.0;
		//olsr->uiRCCount = 0;
		olsr->uiRCNormalCount = 0;
		olsr->uiRCAdvCount = 0;

		olsr->dRecentRCStartTime = 0.0;
		olsr->dRecentRCEndTime = 0.0;


        // Initialisation of differents tables to be used.
        OlsrInitTables(olsr);

        olsr->interfaceSequenceNumbers = (UInt16 *)MEM_malloc(
                                                 sizeof(UInt16)
                                                 * (node->numberInterfaces));

        memset(
            olsr->interfaceSequenceNumbers,
            0,
            sizeof(UInt16) * (node->numberInterfaces));

        // Init interface seq no
        for (index = 0; index < node->numberInterfaces; index++)
        {
            olsr->interfaceSequenceNumbers[index] = 1;
        }
        BOOL retVal = FALSE;
        char buf[MAX_STRING_LENGTH];

        olsr->ip_version = networkType;

        if (networkType == NETWORK_IPV4)
        {
            IO_ReadString(
                node->nodeId,
                NetworkIpGetInterfaceAddress(node, interfaceIndex),
                nodeInput,
                "OLSR-HELLO-INTERVAL",
                &retVal,
                buf);
        }

        else
        {
            Address address;

            NetworkGetInterfaceInfo(
                node,
                interfaceIndex,
                &address,
                olsr->ip_version);

            IO_ReadString(
                node->nodeId,
                &address.interfaceAddr.ipv6,
                nodeInput,
                "OLSR-HELLO-INTERVAL",
                &retVal,
                buf);
        }



        if (retVal)
        {
            olsr->hello_interval = TIME_ConvertToClock(buf);

            if (olsr->hello_interval <= 0 )
            {
                sprintf(errStr, "Invalid Hello Interval"
                            " Parameter specified, hence continuing"
                            " with the default value: %" TYPES_64BITFMT 
                            "dS. \n",
                            DEFAULT_HELLO_INTERVAL / SECOND);
                ERROR_ReportWarning(errStr);

                olsr->hello_interval = DEFAULT_HELLO_INTERVAL;
            }
        }
        else
        {
            olsr->hello_interval = DEFAULT_HELLO_INTERVAL;
        }
        retVal = FALSE;

        if (networkType == NETWORK_IPV4)
        {
            IO_ReadString(
                node->nodeId,
                NetworkIpGetInterfaceAddress(node, interfaceIndex),
                nodeInput,
                "OLSR-TC-INTERVAL",
                &retVal,
                buf);
        }

        else
        {
            Address address;

            NetworkGetInterfaceInfo(
                node,
                interfaceIndex,
                &address,
                olsr->ip_version);

            IO_ReadString(
                node->nodeId,
                &address.interfaceAddr.ipv6,
                nodeInput,
                "OLSR-TC-INTERVAL",
                &retVal,
                buf);
        }

        if (retVal)
        {
            olsr->tc_interval = TIME_ConvertToClock(buf);

            if (olsr->tc_interval <= 0 )
            {
                sprintf(errStr, "Invalid TC Interval"
                            " Parameter specified, hence continuing"
                            " with the default value: %" TYPES_64BITFMT 
                            "dS. \n",
                            DEFAULT_TC_INTERVAL / SECOND);
                ERROR_ReportWarning(errStr);

                olsr->tc_interval = DEFAULT_TC_INTERVAL;
            }
        }
        else
        {
            olsr->tc_interval = DEFAULT_TC_INTERVAL;
        }
        retVal = FALSE;

        if (networkType == NETWORK_IPV4)
        {
            IO_ReadString(
                node->nodeId,
                NetworkIpGetInterfaceAddress(node, interfaceIndex),
                nodeInput,
                "OLSR-MID-INTERVAL",
                &retVal,
                buf);
        }

        else
        {
            Address address;

            NetworkGetInterfaceInfo(
                node,
                interfaceIndex,
                &address,
                olsr->ip_version);

            IO_ReadString(
                node->nodeId,
                &address.interfaceAddr.ipv6,
                nodeInput,
                "OLSR-MID-INTERVAL",
                &retVal,
                buf);
        }

        if (retVal)
        {
            olsr->mid_interval = TIME_ConvertToClock(buf);

            if (olsr->mid_interval <= 0 )
            {
                sprintf(errStr, "Invalid MID Interval"
                            " Parameter specified, hence continuing"
                            " with the default value: %" TYPES_64BITFMT 
                            "dS. \n",
                            DEFAULT_MID_INTERVAL / SECOND);
                ERROR_ReportWarning(errStr);

                olsr->mid_interval = DEFAULT_MID_INTERVAL;
            }
        }
        else
        {
            olsr->mid_interval = DEFAULT_MID_INTERVAL;
        }
        retVal = FALSE;

        if (networkType == NETWORK_IPV4)
        {
            IO_ReadString(
                node->nodeId,
                NetworkIpGetInterfaceAddress(node, interfaceIndex),
                nodeInput,
                "OLSR-HNA-INTERVAL",
                &retVal,
                buf);
        }

        else
        {
            Address address;

            NetworkGetInterfaceInfo(
                node,
                interfaceIndex,
                &address,
                olsr->ip_version);

            IO_ReadString(
                node->nodeId,
                &address.interfaceAddr.ipv6,
                nodeInput,
                "OLSR-HNA-INTERVAL",
                &retVal,
                buf);
        }

        if (retVal)
        {
            olsr->hna_interval = TIME_ConvertToClock(buf);

            if (olsr->hna_interval <= 0 )
            {
                sprintf(errStr, "Invalid HNA Interval"
                            " Parameter specified, hence continuing"
                            " with the default value: %" TYPES_64BITFMT 
                            "dS. \n",
                            DEFAULT_HNA_INTERVAL / SECOND);
                ERROR_ReportWarning(errStr);

                olsr->hna_interval = DEFAULT_HNA_INTERVAL;
            }
        }
        else
        {
            olsr->hna_interval = DEFAULT_HNA_INTERVAL;
        }
        retVal = FALSE;

        if (networkType == NETWORK_IPV4)
        {
            IO_ReadString(
                node->nodeId,
                NetworkIpGetInterfaceAddress(node, interfaceIndex),
                nodeInput,
                "OLSR-NEIGHBOR-HOLD-TIME",
                &retVal,
                buf);
        }

        else
        {
            Address address;

            NetworkGetInterfaceInfo(
                node,
                interfaceIndex,
                &address,
                olsr->ip_version);

            IO_ReadString(
                node->nodeId,
                &address.interfaceAddr.ipv6,
                nodeInput,
                "OLSR-NEIGHBOR-HOLD-TIME",
                &retVal,
                buf);
        }

        if (retVal)
        {
            olsr->neighb_hold_time = TIME_ConvertToClock(buf);

            if (olsr->neighb_hold_time <= 0 )
            {
                sprintf(errStr, "Invalid NEIGHBOR-HOLD Interval"
                            " Parameter specified, hence continuing"
                            " with the default value: %" TYPES_64BITFMT 
                            "dS. \n",
                            DEFAULT_NEIGHB_HOLD_TIME / SECOND);
                ERROR_ReportWarning(errStr);

                olsr->neighb_hold_time = DEFAULT_NEIGHB_HOLD_TIME;
            }
        }
        else
        {

            olsr->neighb_hold_time = DEFAULT_NEIGHB_HOLD_TIME;
        }
        retVal = FALSE;

        if (networkType == NETWORK_IPV4)
        {
            IO_ReadString(
                node->nodeId,
                NetworkIpGetInterfaceAddress(node, interfaceIndex),
                nodeInput,
                "OLSR-TOPOLOGY-HOLD-TIME",
                &retVal,
                buf);
        }

        else
        {
            Address address;

            NetworkGetInterfaceInfo(
                node,
                interfaceIndex,
                &address,
                olsr->ip_version);

            IO_ReadString(
                node->nodeId,
                &address.interfaceAddr.ipv6,
                nodeInput,
                "OLSR-TOPOLOGY-HOLD-TIME",
                &retVal,
                buf);
        }

        if (retVal)
        {
            olsr->top_hold_time = TIME_ConvertToClock(buf);

            if (olsr->top_hold_time <= 0 )
            {
                sprintf(errStr, "Invalid TOP-HOLD Interval"
                            " Parameter specified, hence continuing"
                            " with the default value: %" TYPES_64BITFMT 
                            "dS. \n",
                            DEFAULT_TOP_HOLD_TIME / SECOND);
                ERROR_ReportWarning(errStr);

                olsr->top_hold_time = DEFAULT_TOP_HOLD_TIME;
            }
        }
        else
        {
            olsr->top_hold_time = DEFAULT_TOP_HOLD_TIME;
        }
        retVal = FALSE;

        if (networkType == NETWORK_IPV4)
        {
            IO_ReadString(
                node->nodeId,
                NetworkIpGetInterfaceAddress(node, interfaceIndex),
                nodeInput,
                "OLSR-DUPLICATE-HOLD-TIME",
                &retVal,
                buf);
        }

        else
        {
            Address address;

            NetworkGetInterfaceInfo(
                node,
                interfaceIndex,
                &address,
                olsr->ip_version);

            IO_ReadString(
                node->nodeId,
                &address.interfaceAddr.ipv6,
                nodeInput,
                "OLSR-DUPLICATE-HOLD-TIME",
                &retVal,
                buf);
        }

        if (retVal)
        {
            olsr->dup_hold_time = TIME_ConvertToClock(buf);

            if (olsr->dup_hold_time <= 0 )
            {
                sprintf(errStr, "Invalid DUPLICATE-HOLD Interval"
                            " Parameter specified, hence continuing"
                            " with the default value: %" TYPES_64BITFMT 
                            "dS. \n",
                            DEFAULT_DUPLICATE_HOLD_TIME / SECOND);
                ERROR_ReportWarning(errStr);

                olsr->dup_hold_time = DEFAULT_DUPLICATE_HOLD_TIME;
            }
        }
        else
        {
            olsr->dup_hold_time = DEFAULT_DUPLICATE_HOLD_TIME;
        }
        retVal = FALSE;

        if (networkType == NETWORK_IPV4)
        {
            IO_ReadString(
                node->nodeId,
                NetworkIpGetInterfaceAddress(node, interfaceIndex),
                nodeInput,
                "OLSR-MID-HOLD-TIME",
                &retVal,
                buf);
        }

        else
        {
            Address address;

            NetworkGetInterfaceInfo(
                node,
                interfaceIndex,
                &address,
                olsr->ip_version);

            IO_ReadString(
                node->nodeId,
                &address.interfaceAddr.ipv6,
                nodeInput,
                "OLSR-MID-HOLD-TIME",
                &retVal,
                buf);
        }

        if (retVal)
        {
            olsr->mid_hold_time = TIME_ConvertToClock(buf);

            if (olsr->mid_hold_time <= 0 )
            {
                sprintf(errStr, "Invalid MID-HOLD Interval"
                            " Parameter specified, hence continuing"
                            " with the default value: %" TYPES_64BITFMT
                            "dS. \n",
                            DEFAULT_MID_HOLD_TIME / SECOND);
                ERROR_ReportWarning(errStr);

                olsr->mid_hold_time = DEFAULT_MID_HOLD_TIME;
            }
        }
        else
        {
            olsr->mid_hold_time = DEFAULT_MID_HOLD_TIME;
        }
        retVal = FALSE;

        if (networkType == NETWORK_IPV4)
        {
            IO_ReadString(
                node->nodeId,
                NetworkIpGetInterfaceAddress(node, interfaceIndex),
                nodeInput,
                "OLSR-HNA-HOLD-TIME",
                &retVal,
                buf);
        }

        else
        {
            Address address;

            NetworkGetInterfaceInfo(
                node,
                interfaceIndex,
                &address,
                olsr->ip_version);

            IO_ReadString(
                node->nodeId,
                &address.interfaceAddr.ipv6,
                nodeInput,
                "OLSR-HNA-HOLD-TIME",
                &retVal,
                buf);
        }

        if (retVal)
        {
            olsr->hna_hold_time = TIME_ConvertToClock(buf);

            if (olsr->hna_hold_time <= 0 )
            {
                sprintf(errStr, "Invalid HNA-HOLD Interval"
                            " Parameter specified, hence continuing"
                            " with the default value: %" TYPES_64BITFMT 
                            "dS. \n",
                            DEFAULT_HNA_HOLD_TIME / SECOND);
                ERROR_ReportWarning(errStr);

                olsr->hna_hold_time = DEFAULT_HNA_HOLD_TIME;
            }
        }
        else
        {
            olsr->hna_hold_time = DEFAULT_HNA_HOLD_TIME;
        }

        clocktype delay = OLSR_STARTUP_DELAY
                          - (RANDOM_nrand(olsr->seed)
                          % (clocktype) ((Float32) OLSR_STARTUP_DELAY
                                                   * OLSR_STARTUP_JITTER));

        // set refresh timer for hello message
        Message* helloPeriodicMsg = MESSAGE_Alloc(node,
                                      APP_LAYER,
                                      APP_ROUTING_OLSR_INRIA,
                                      MSG_APP_OlsrPeriodicHello);

        MESSAGE_Send(node, helloPeriodicMsg, delay);

       // set refresh timer for tc message
        Message* tcPeriodicMsg = MESSAGE_Alloc(node,
                                     APP_LAYER,
                                     APP_ROUTING_OLSR_INRIA,
                                     MSG_APP_OlsrPeriodicTc);

        MESSAGE_Send(node, tcPeriodicMsg, delay);

        // set refresh timer for mid message
        Message* midPeriodicMsg = MESSAGE_Alloc(node,
                                      APP_LAYER,
                                      APP_ROUTING_OLSR_INRIA,
                                      MSG_APP_OlsrPeriodicMid);

        MESSAGE_Send(node, midPeriodicMsg, delay);

        // set refresh timer for hna message
        Message* hnaPeriodicMsg = MESSAGE_Alloc(node,
                                      APP_LAYER,
                                      APP_ROUTING_OLSR_INRIA,
                                      MSG_APP_OlsrPeriodicHna);

        MESSAGE_Send(node, hnaPeriodicMsg, delay);


        // set neighbor hold timer
        Message* neighHoldMsg = MESSAGE_Alloc(node,
                                    APP_LAYER,
                                    APP_ROUTING_OLSR_INRIA,
                                    MSG_APP_OlsrNeighHoldTimer);

        MESSAGE_Send(node, neighHoldMsg, olsr->neighb_hold_time);


        // set topology hold timer
        Message* topoHoldMsg = MESSAGE_Alloc(node,
                                   APP_LAYER,
                                   APP_ROUTING_OLSR_INRIA,
                                   MSG_APP_OlsrTopologyHoldTimer);

        MESSAGE_Send(node, topoHoldMsg, olsr->top_hold_time);

        // set duplicate hold timer
        Message* duplicateHoldMsg = MESSAGE_Alloc(node,
                                        APP_LAYER,
                                        APP_ROUTING_OLSR_INRIA,
                                        MSG_APP_OlsrDuplicateHoldTimer);

        MESSAGE_Send(node, duplicateHoldMsg, olsr->dup_hold_time);

        // set MID hold timer
        Message* midHoldMsg = MESSAGE_Alloc(node,
                                  APP_LAYER,
                                  APP_ROUTING_OLSR_INRIA,
                                  MSG_APP_OlsrMidHoldTimer);

        MESSAGE_Send(node, midHoldMsg, olsr->mid_hold_time);

        // set HNA hold timer
        Message* hnaHoldMsg = MESSAGE_Alloc(node,
                                  APP_LAYER,
                                  APP_ROUTING_OLSR_INRIA,
                                  MSG_APP_OlsrHnaHoldTimer);

        MESSAGE_Send(node, hnaHoldMsg, olsr->hna_hold_time);


        NetworkGetInterfaceInfo(
            node, interfaceIndex, &olsr->main_address, networkType);

        // Intialize trace
        OlsrInitTrace(node, nodeInput);

    }
}


// /**
// FUNCTION   :: RoutingOlsrPrintStat
// LAYER      :: APPLICATION
// PURPOSE    :: Print the statistics
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// RETURN :: void : NULL
// **/

static
void RoutingOlsrPrintStat(Node *node)
{
    RoutingOlsrStat olsrStat;
    RoutingOlsr *olsr;
    char buf[MAX_STRING_LENGTH];

    olsr = (RoutingOlsr* ) node->appData.olsr;
    olsrStat = olsr->olsrStat;

    if (node->appData.routingStats)
    {
        sprintf(buf, "Hello Messages Received = %u",
                olsrStat.numHelloReceived);

        IO_PrintStat(
            node,
            "Application",
            "OLSR",
            ANY_DEST,
            -1, // instance Id
            buf);
        sprintf(buf, "Hello Messages Sent = %u",
                olsrStat.numHelloSent);

        IO_PrintStat(
            node,
            "Application",
            "OLSR",
            ANY_DEST,
            -1, // instance Id
            buf);
        sprintf(buf, "TC Messages Received = %u",
                olsrStat.numTcReceived);

        IO_PrintStat(
            node,
            "Application",
            "OLSR",
            ANY_DEST,
            -1, // instance Id
            buf);
        sprintf(buf, "TC Messages Generated = %u",
                olsrStat.numTcGenerated);

        IO_PrintStat(
            node,
            "Application",
            "OLSR",
            ANY_DEST,
            -1, // instance Id
            buf);
        sprintf(buf, "TC Messages Relayed = %u",
                olsrStat.numTcRelayed);

        IO_PrintStat(
            node,
            "Application",
            "OLSR",
            ANY_DEST,
            -1, // instance Id
            buf);
        sprintf(buf, "MID Messages Received = %u",
                olsrStat.numMidReceived);

        IO_PrintStat(
            node,
            "Application",
            "OLSR",
            ANY_DEST,
            -1, // instance Id
            buf);
        sprintf(buf, "MID Messages Generated = %u",
                olsrStat.numMidGenerated);

        IO_PrintStat(
            node,
            "Application",
            "OLSR",
            ANY_DEST,
            -1, // instance Id
            buf);
        sprintf(buf, "MID Messages Relayed = %u",
                olsrStat.numMidRelayed);

        IO_PrintStat(
            node,
            "Application",
            "OLSR",
            ANY_DEST,
            -1, // instance Id
            buf);
        sprintf(buf, "HNA Messages Received = %u",
                olsrStat.numHnaReceived);

        IO_PrintStat(
            node,
            "Application",
            "OLSR",
            ANY_DEST,
            -1, // instance Id
            buf);
        sprintf(buf, "HNA Messages Generated = %u",
                olsrStat.numHnaGenerated);

        IO_PrintStat(
            node,
            "Application",
            "OLSR",
            ANY_DEST,
            -1, // instance Id
            buf);
        sprintf(buf, "HNA Messages Relayed = %u",
                olsrStat.numHnaRelayed);

        IO_PrintStat(
            node,
            "Application",
            "OLSR",
            ANY_DEST,
            -1, // instance Id
            buf);

    }
}

// /**
// FUNCTION   :: RoutingOlsrInriaFinalize
// LAYER      :: APPLICATION
// PURPOSE    :: Called at the end of simulation to collect the results of
//               the simulation of the OLSR routing protocol.
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + interfaceId : Int32 : interface index
// RETURN :: void : NULL
// **/
void RoutingOlsrInriaFinalize(Node * node, Int32 interfaceId)
{
    //Peter added for support..

	if (g_iNeighborChangeCnt != -1 || g_iTopologyChangeCnt != -1 || g_iBothChg != -1)
	{
		memset(g_szText, 0, 4096 * sizeof(char));

		sprintf(g_szText, "\n\n");

		sprintf(g_szText, "%sg_iNeighborChangeCnt = %d, g_iTopologyChangeCnt = %d, g_iBothChg = %d \n", g_szText,
			g_iNeighborChangeCnt, g_iTopologyChangeCnt, g_iBothChg);


		sprintf(g_szText, "%s\n\n", g_szText);

		sprintf(g_szText, "%sg_iNeighborChgByOlsrInsertMidAlias = %d, \n g_iNeighborChgByOlsrTimeoutLinkEntry = %d, g_iNeighborChgByOlsrTimeout2HopNeighbors = %d, \n g_iNeighborChgByOlsrProcessNeighborsInHelloMsg = %d, g_iNeighborChgByOlsrProcessReceivedHello = %d \n", g_szText,
			g_iNeighborChgByOlsrInsertMidAlias, //g_iNeighborChgByOlsrUpdateNeighborStatus, 
			g_iNeighborChgByOlsrTimeoutLinkEntry, g_iNeighborChgByOlsrTimeout2HopNeighbors,
			g_iNeighborChgByOlsrProcessNeighborsInHelloMsg, g_iNeighborChgByOlsrProcessReceivedHello);


		sprintf(g_szText, "%s\n\n", g_szText);

		sprintf(g_szText, "%sg_iTopologyChgByOlsrInsertMidAlias = %d, g_iTopologyChgByOlsrUpdateHnaEntry = %d,\n g_iTopologyChgByOlsrTimeout2HopNeighbors = %d, \n g_iTopologyChgByOlsrUpdateLastTable = %d g_iTopologyChgByOlsrTimeoutTopologyTable = %d, \n g_iTopologyChgByOlsrProcessNeighborsInHelloMsg = %d, g_iTopologyChgByOlsrProcessReceivedHello = %d, \n g_iTopologyChgByOlsrProcessReceivedMid = %d, g_iTopologyChgByOlsrProcessReceivedTc = %d \n g_iTopologyChgByOlsrProcessReceivedTcAddNew = %d, g_iTopologyChgByOlsrProcessReceivedTcDeleteOld = %d \n", g_szText,
			g_iTopologyChgByOlsrInsertMidAlias, g_iTopologyChgByOlsrUpdateHnaEntry,
			//g_iTopologyChgByOlsrUpdateNeighborStatus, 
			g_iTopologyChgByOlsrTimeout2HopNeighbors,
			g_iTopologyChgByOlsrUpdateLastTable, 
			g_iTopologyChgByOlsrTimeoutTopologyTable,
			g_iTopologyChgByOlsrProcessNeighborsInHelloMsg, g_iTopologyChgByOlsrProcessReceivedHello,
			g_iTopologyChgByOlsrProcessReceivedMid, g_iTopologyChgByOlsrProcessReceivedTc,
			g_iTopologyChgByOlsrProcessReceivedTcAddNew, g_iTopologyChgByOlsrProcessReceivedTcDeleteOld			
			);


		sprintf(g_szText, "%sg_iTopologyChgApplyNormal = %d      g_iTopologyChgApplyARC = %d      g_iNeighborhoodChgApplyARC = %d \n", 
			g_szText, g_iTopologyChgApplyNormal, g_iTopologyChgApplyARC, g_iNeighborhoodChgApplyARC);

		

		/*
		sprintf(g_szText, "%sg_iTopologyChgApplyARC_With_Delete = %d, g_iTopologyChgApplyARC_With_Delete_Success = %d, g_iTopologyChgApplyARC_With_Delete_Failed_Cause_Rediscovery = %d \n", 
			g_szText, g_iTopologyChgApplyARC_With_Delete, g_iTopologyChgApplyARC_With_Delete_Success, g_iTopologyChgApplyARC_With_Delete_Failed_Cause_Rediscovery);
		*/


		//if (FALSE)
		if (FORWARD_WITH_PURE_ROUTE_TABLE == 1)
		{
			
			//if (fp_rtrace == NULL)
			{
				FILE* fpi = fopen("sub.file", "r");
				if (!fpi) 
				{

				}
				else
				{

					char sLine[MAX_PATH] = {0};

					char sEqualSign[MAX_PATH] = {0};
					char sTmp[MAX_PATH] = {0};

					char szMatchEXPERIMENTNAME[MAX_PATH] = "EXPERIMENT-NAME";

					while(!feof(fpi))
					{ 

						ZeroMemory(sLine, MAX_PATH * sizeof(char));

						fgets(sLine, MAX_PATH, fpi);

						ZeroMemory(sTmp, MAX_PATH * sizeof(char));
						ZeroMemory(sEqualSign, MAX_PATH * sizeof(char));


						if (0 == strncmp(sLine, szMatchEXPERIMENTNAME, strlen(szMatchEXPERIMENTNAME)))
						{
							sscanf(sLine + strlen(szMatchEXPERIMENTNAME), "%s", sTmp);

							//NODE_ID_FOR_TEST_START = atoi(sTmp);
							//printf("g_OverallipOutNoRoutes = %d \n", g_OverallipOutNoRoutes);

							FILE* fpiii = fopen(sTmp, "a");

							if (fpiii)
							{
								fprintf(fpiii, "g_OverallipOutNoRoutes = %d \n", g_OverallipOutNoRoutes);
								//fprintf(fpiii, "g_iToAchieveSameRoute = %d, g_iAccumulativeRouteCalculation = %d  \n", g_iToAchieveSameRoute, g_iAccumulativeRouteCalculation);

								fclose(fpiii);
							}



						}
					}

					fclose(fpi);
				}
			}
			
			
			
		}
		

		printf("SEED = %d, g_OverallipOutNoRoutes = %d g_iMobilitySpeed = %d g_iAccumulativeRouteCalculation = %d \n", 
			node->globalSeed, g_OverallipOutNoRoutes, g_iMobilitySpeed, g_iAccumulativeRouteCalculation);

		


		g_iNeighborChangeCnt = -1;
		g_iTopologyChangeCnt = -1;

		g_iBothChg = -1;

	}
	

	
	
	
	RoutingOlsr*  olsr = (RoutingOlsr* ) node->appData.olsr;
    if (!olsr->statsPrinted)
    {
        RoutingOlsrPrintStat(node);
        olsr->statsPrinted = TRUE;

        if (DEBUG_OUTPUT)
        {
			//Peter modified 
			//OlsrPrintTables(node);
            //NetworkPrintForwardingTable(node);
        
			//OlsrPrintRoutingTable(olsr->routingtable);
		}
    }


	if (g_iRunTimeCompare == 1)
	{
		
		if (olsr->pszInfo != NULL)
		{
			delete [] olsr->pszInfo;
			olsr->pszInfo = NULL;
		}

		if (olsr->pszOrigRT != NULL)
		{
			delete [] olsr->pszOrigRT;
			olsr->pszOrigRT = NULL;
		}

		if (olsr->pszMiddleRT != NULL)
		{
			delete [] olsr->pszMiddleRT;
			olsr->pszMiddleRT = NULL;
		}

		if (olsr->pszRTWithARC != NULL)
		{
			delete [] olsr->pszRTWithARC;
			olsr->pszRTWithARC = NULL;
		}

		if (olsr->pszRTWithoutARC != NULL)
		{
			delete [] olsr->pszRTWithoutARC;
			olsr->pszRTWithoutARC = NULL;
		}
		

		if (olsr->pszOtherTables != NULL)
		{
			delete [] olsr->pszOtherTables;
			olsr->pszOtherTables = NULL;
		}

	}


	if (_TEST_TIME_COMPLEXITY)
	//if (_TEST_TIME_COMPLEXITY && g_strTxt != NULL)
	{
		
		FILE* fp = NULL;

		char sTmp[MAX_PATH] = {0};

		ZeroMemory(sTmp, MAX_PATH * sizeof(char));

		sprintf(sTmp, "Speed-%d", g_iMobilitySpeed);

		if (_OLSR_MULTIPATH)
		{

			sprintf(sTmp, "%s-%s-EstimateTimeComplexity_MP", sTmp, g_szRoot);

		}
		else
		{

			sprintf(sTmp, "%s-%s-EstimateTimeComplexity_SP", sTmp, g_szRoot);

		}

		sprintf(sTmp, "%s_ARC_%d_%d", sTmp, g_iAccumulativeRouteCalculation, g_iToAchieveSameRoute);


		fp = fopen(sTmp, "a");
			

		if (!fp)
		{
			ERROR_ReportError("Can't open EstimateTimeComplexity \n");
		}
		else
		{

			char sOutputStemStr[MAX_PATH] = {0};

			ZeroMemory(sOutputStemStr, MAX_PATH * sizeof(char));

			if (_OLSR_MULTIPATH)
			{
				
				sprintf(sOutputStemStr, "OlsrCalculateRoutingTableForMultiPath");
			}
			else
			{
				sprintf(sOutputStemStr, "OlsrCalculateRoutingTable");
			}

			
			if (g_iSimplifiedTimeTest == 1)
			{
				char sOutputStr[MAX_PATH] = {0};

				ZeroMemory(sOutputStr, MAX_PATH * sizeof(char));



				sprintf(sOutputStr, "%s", sOutputStemStr);

				/*
				if (ptti->bIsAdvOrNot)
				{
					sprintf(sOutputStr, "%sAdv", sOutputStr);
				}
				else
				{
					sprintf(sOutputStr, "%s___", sOutputStr);
				}
				*/

				double dAvgRealRunTime = olsr->dRCRealRuntime / (double)(olsr->uiRCNormalCount + olsr->uiRCAdvCount);

				sprintf(sOutputStr, "%s for node %d : ", sOutputStr, node->nodeId);
				sprintf(sOutputStr, "%s     dRCRealRuntime =         %f           uiRCNormalCount =        %d          uiRCAdvCount = %d          dAvgRealRunTime = %f \n", 
					sOutputStr, olsr->dRCRealRuntime, olsr->uiRCNormalCount, olsr->uiRCAdvCount, dAvgRealRunTime);

				fprintf(fp, "%s", sOutputStr);
			}
			else
			{
				for (int i = 0; i < olsr->iTcItemCnt; i++)
				{

					tc_trace_item * ptti = &(olsr->pvt_TTIs[i]);

					char sOutputStr[MAX_PATH] = {0};

					ZeroMemory(sOutputStr, MAX_PATH * sizeof(char));



					sprintf(sOutputStr, "%s", sOutputStemStr);



					if (ptti->bIsAdvOrNot)
					{
						sprintf(sOutputStr, "%sAdv", sOutputStr);
					}
					else
					{
						sprintf(sOutputStr, "%s___", sOutputStr);
					}

					sprintf(sOutputStr, "%s for node %d : ", sOutputStr, node->nodeId);
					sprintf(sOutputStr, "%s      CurrentSimTime =        %f            RealTimeSpent =         %f           CombinedCnt =        %d  \n", sOutputStr, ptti->dCurrentSimTime, ptti->dRealTimeDuration, ptti->iCombinedCnt);

					fprintf(fp, "%s", sOutputStr);
				}



				if (olsr->iTcItemSize != 0)
				{

					delete [] olsr->pvt_TTIs;
				}
			}


			
			if (node->nodeId == NODE_ID_FOR_TEST_END)
			{
				fprintf(fp, "%s", g_szText);
				
			}
			
			//fprintf(fp, "%s", g_strTxt);

			fclose(fp);
		}

	


		if (node->nodeId == NODE_ID_FOR_TEST_END)
		{
			if (g_szRoot != NULL)
			{
				delete [] g_szRoot;

				g_szRoot = NULL;
			}
			

			/*
			if (g_strTxt != NULL)
			{
				
				delete [] g_strTxt;
				g_strTxt = NULL;
			}
			*/
		}
		

		
	}
}

// /**
// FUNCTION   :: RoutingOlsrInriaLayer
// LAYER      :: APPLICATION
// PURPOSE    :: The main layer structure routine, called from application.cpp
// PARAMETERS ::
// + node : Node* : Pointer to Node structure
// + msg : Message* : Message to be handled
// RETURN :: void : NULL
// **/
void RoutingOlsrInriaLayer(Node *node, Message *msg)
{
    unsigned char index;
    RoutingOlsr*  olsr = (RoutingOlsr* ) node->appData.olsr;
    if(olsr == NULL)
    {
        MESSAGE_Free(node, msg);
        return;
    }

     switch (msg->eventType)
    {
        case MSG_APP_OlsrPeriodicHello:
        {
            // hello periodic message expired. Generate hello message
            // and set same timer for next refresh. For all OLSR interfaces
            // call OlsrGenerateHello

            if (DEBUG)
            {
                printf ("Generating Hellos for Node %d on all"
                    " olsr-interfaces\n", node->nodeId);
            }

            for (index = 0; index < node->numberInterfaces; index++)
            {
                // Do not consider  non-olsr interfaces
                if (NetworkIpGetUnicastRoutingProtocolType(node,
                    index, olsr->ip_version) == ROUTING_PROTOCOL_OLSR_INRIA)
                {
                   OlsrGenerateHello(node,index);
                }
            }

            MESSAGE_Free(node, msg);

            // set refresh timer for hello message
            Message* helloPeriodicMsg = MESSAGE_Alloc(node,
                                            APP_LAYER,
                                            APP_ROUTING_OLSR_INRIA,
                                            MSG_APP_OlsrPeriodicHello);

            MESSAGE_Send(node, helloPeriodicMsg, olsr->hello_interval);

            break;
        }
        
		case MSG_APP_OlsrPeriodicTc:
        {
            // tc periodic message expired. Generate tc message and set
            // same timer for next refresh

            // For all olsr interfaces
            // generate tc

            if (DEBUG)
            {
                printf ("Generating TC for Node %d on all olsr-interfaces\n",
                                                               node->nodeId);
            }

            for (index = 0; index < node->numberInterfaces; index++)
            {
                // Do not consider  non-olsr interfaces
                if (NetworkIpGetUnicastRoutingProtocolType(node,
                    index, olsr->ip_version) == ROUTING_PROTOCOL_OLSR_INRIA)
                {
                    //Calling for TC generation
                    OlsrGenerateTc(node, index);
                }
            }
            MESSAGE_Free(node, msg);

            // set refresh timer for tc message
            Message* tcPeriodicMsg = MESSAGE_Alloc(node,
                                        APP_LAYER,
                                        APP_ROUTING_OLSR_INRIA,
                                        MSG_APP_OlsrPeriodicTc);

            MESSAGE_Send(node, tcPeriodicMsg, olsr->tc_interval);

            break;
        }
        
		case MSG_APP_OlsrPeriodicMid:
        {
            RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;
            // Generate and send MID message for multiple olsr-interfaces
            if (olsr->numOlsrInterfaces <= 1)
            {
                MESSAGE_Free(node, msg);
                break;
            }
            // Mid periodic message expired. Generate mid message and set
            // same timer for next refresh

            if (DEBUG)
            {
                printf ("Generating Mid  for Node %d on all"
                    " olsr-interfaces\n", node->nodeId);
            }

            for (index = 0; index < node->numberInterfaces; index++)
            {
                // Do not consider  non-olsr interfaces
                if (NetworkIpGetUnicastRoutingProtocolType(node,
                    index, olsr->ip_version) == ROUTING_PROTOCOL_OLSR_INRIA)
                {
                    OlsrGenerateMid(node, index);
                }
            }

            MESSAGE_Free(node, msg);

            // set refresh timer for mid message
            Message* midPeriodicMsg = MESSAGE_Alloc(node,
                                          APP_LAYER,
                                          APP_ROUTING_OLSR_INRIA,
                                          MSG_APP_OlsrPeriodicMid);

            MESSAGE_Send(node, midPeriodicMsg, olsr->mid_interval);

            break;
        }

        case MSG_APP_OlsrPeriodicHna:
        {
            RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;
            // Generate and send HNA message having non olsr-interfaces
            int noOfQualifiedInterfaces = 0;
            for (index = 0; index < node->numberInterfaces; index++)
            {
                if (NetworkIpGetInterfaceType(node, index)== olsr->ip_version
                   || NetworkIpGetInterfaceType(node, index) == NETWORK_DUAL)
                {
                    noOfQualifiedInterfaces++;
                }
            }
            if (olsr->numOlsrInterfaces == noOfQualifiedInterfaces)
            {
                MESSAGE_Free(node, msg);
                break;
            }
            // HNA periodic message expired. Generate hna message and set
            // same timer for next refresh

            if (DEBUG)
            {
                printf ("Generating Hna for Node %d on all"
                    " olsr-interfaces\n", node->nodeId);
            }

            for (index = 0; index < node->numberInterfaces; index++)
            {
                // Do not consider  non-olsr interfaces
                if (NetworkIpGetUnicastRoutingProtocolType(node,
                    index, olsr->ip_version) == ROUTING_PROTOCOL_OLSR_INRIA)
                {
                    OlsrGenerateHna(node, index);
                }
            }

            MESSAGE_Free(node, msg);

            // set refresh timer for mid message
            Message* hnaPeriodicMsg = MESSAGE_Alloc(node,
                                          APP_LAYER,
                                          APP_ROUTING_OLSR_INRIA,
                                          MSG_APP_OlsrPeriodicHna);

            MESSAGE_Send(node, hnaPeriodicMsg, olsr->hna_interval);

            break;
        }
        
		case MSG_APP_FromTransport:
        {
            // OLSR message received from Transport layer
            RoutingOlsrHandlePacket(node, msg);
            MESSAGE_Free(node, msg);
            break;
        }

        case MSG_APP_OlsrNeighHoldTimer:
        {
            // neighbor hold timer message expired. Refresh MPR selector and
            // neighbor table and resend send the hold timer message again

            Message *neighHoldMsg;

            OlsrTimeoutMprSelectorTable(node);

            if (DEBUG)
            {
                OlsrPrintLinkSet(node);
            }
            OlsrTimeoutLinkEntry(node);

            if (DEBUG)
            {
                OlsrPrintLinkSet(node);
            }
            OlsrTimeoutNeighborhoodTables(node);
            OlsrProcessChanges(node);

            MESSAGE_Free(node, msg);
            neighHoldMsg = MESSAGE_Alloc(node,
                                    APP_LAYER,
                                    APP_ROUTING_OLSR_INRIA,
                                    MSG_APP_OlsrNeighHoldTimer);

            MESSAGE_Send(node, neighHoldMsg, olsr->neighb_hold_time);
            break;
        }

        case MSG_APP_OlsrTopologyHoldTimer:
        {
            // topology hold timer message expired. Refresh topology table and
            // resend send the hold timer message again

            Message* topoHoldMsg;

            OlsrTimeoutTopologyTable(node);
            OlsrProcessChanges(node);

            MESSAGE_Free(node, msg);
            topoHoldMsg = MESSAGE_Alloc(node,
                                    APP_LAYER,
                                    APP_ROUTING_OLSR_INRIA,
                                    MSG_APP_OlsrTopologyHoldTimer);

            MESSAGE_Send(node, topoHoldMsg, olsr->top_hold_time);
            break;
        }

        case MSG_APP_OlsrDuplicateHoldTimer:
        {
            // duplicate hold timer message expired. Refresh duplicate table
            // and resend send the hold timer message again

            Message *duplicateHoldMsg;

            OlsrTimeoutDuplicateTable(node);
            OlsrProcessChanges(node);

            MESSAGE_Free(node, msg);
            duplicateHoldMsg = MESSAGE_Alloc(node,
                                    APP_LAYER,
                                    APP_ROUTING_OLSR_INRIA,
                                    MSG_APP_OlsrDuplicateHoldTimer);

            MESSAGE_Send(node,
                         duplicateHoldMsg,
                         olsr->dup_hold_time);
            break;
        }

        case MSG_APP_OlsrMidHoldTimer:
        {
            // mid hold timer message expired. Refresh mid table
            // and resend send the hold timer message again

            Message* midHoldMsg;

            OlsrTimeoutMidTable(node);
            OlsrProcessChanges(node);

            MESSAGE_Free(node, msg);
            midHoldMsg = MESSAGE_Alloc(node,
                                    APP_LAYER,
                                    APP_ROUTING_OLSR_INRIA,
                                    MSG_APP_OlsrMidHoldTimer);

            MESSAGE_Send(node,
                         midHoldMsg,
                         olsr->mid_hold_time);
            break;
        }
        
		case MSG_APP_OlsrHnaHoldTimer:
        {
            // HNA hold timer message expired. Refresh mid table
            // and resend send the hold timer message again

            Message* hnaHoldMsg;

            OlsrTimeoutHnaTable(node);
            OlsrProcessChanges(node);

            MESSAGE_Free(node, msg);
            hnaHoldMsg = MESSAGE_Alloc(node,
                                    APP_LAYER,
                                    APP_ROUTING_OLSR_INRIA,
                                    MSG_APP_OlsrHnaHoldTimer);

            MESSAGE_Send(node,
                         hnaHoldMsg,
                         olsr->hna_hold_time);
            break;
        }


        default:
        {
            MESSAGE_Free(node, msg);
            // invalid message
            ERROR_Assert(FALSE, "Invalid switch value");
        }
    }
 }

double RetrieveSourceToDestDirection(Node* node, NodeAddress na_dest)
{

	double dWeightedDirection = 0.0;

	rt_entry* destination;
	rthash* routing_hash;

	UInt32 hash;

	RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

	Address aDest;


	SetIPv4AddressInfo(&aDest, na_dest);

	OlsrHashing(aDest, &hash);
	routing_hash = &olsr->routingtable[hash % HASHMASK];

	rt_entry* First_destination = NULL;


	for (destination = routing_hash->rt_back;
		destination != (rt_entry* ) routing_hash;
		destination = destination->rt_back)
	{
		if (destination->rt_hash != hash)
		{

			continue;
		}

		if (First_destination == NULL)
		{
			First_destination = destination;

                        double dRWON = 0.0;

						if (_TEST_TIME_COMPLEXITY)
						{
                             dRWON = First_destination->rt_entry_infos.related_neighbor->neighbor_infos.dDegreeWRTNode;
						}
						else
						{
							
							dRWON = First_destination->rt_entry_infos.rtu_DegreeWRTNode;

						}
						

					dWeightedDirection = RadiusDegreeDifference(First_destination->rt_entry_infos.oa_dWeightedDirectionDiffer + dRWON, 0);
		
			break;
		}
	}

	return dWeightedDirection;
}


rt_entry* QueryRoutingTableAccordingToNodeId(Node* node, NodeAddress na_tc, NodeAddress * pnaRoute, rthash** prhRetrieve, rt_entry** ppre)
{

	//printf("QueryRoutingTableAccordingToNodeId begin \n");

	//Int16 uiConfidentHopCount = -1;

	//return uiConfidentHopCount;

	rt_entry* First_destination = NULL;

	rt_entry* Conclude_destination = NULL;


	rt_entry* destination;
	rthash* routing_hash;

	UInt32 hash;

	RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

	Address aDest;


	SetIPv4AddressInfo(&aDest, na_tc);

	OlsrHashing(aDest, &hash);
	routing_hash = &olsr->routingtable[hash % HASHMASK];

	if (prhRetrieve != NULL)
	{
		*prhRetrieve = routing_hash;
	}


	for (destination = routing_hash->rt_back;
		destination != (rt_entry* ) routing_hash;
		destination = destination->rt_back)
	{
		if (destination->rt_hash != hash)
		{

			continue;
		}

		if (Conclude_destination == NULL)
		{
			//record the first one
			Conclude_destination = destination;

			if (ppre != NULL)
			{
				*ppre = destination;
			}
		}


		if (pnaRoute != NULL)
		{
			if (destination->rt_entry_infos.rtu_router.interfaceAddr.ipv4 != *pnaRoute)
			{
				continue;
			}
			else
			{
				
				
				
			}
			
		}
		else
		{
			// &&  
		}


		if (First_destination == NULL)
		{
			First_destination = destination;

			//uiConfidentHopCount = First_destination->rt_entry_infos.rtu_metric;
			


			break;
		}
	}

	

	
	//printf("QueryRoutingTableAccordingToNodeId end!!!!!!!!!!!!!!!! \n");

	return First_destination;
}

Int16 ProcessRoutingTableAccordingToTC(Node* node, NodeAddress na_tc, BOOL bRemove)
{

	//printf("ProcessRoutingTableAccordingToTC begin \n");


	
	Int16 uiConfidentHopCount = -1;

	//return uiConfidentHopCount;

	rt_entry* destination;
	rthash* routing_hash;

	UInt32 hash;

	RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

	Address aDest;


	SetIPv4AddressInfo(&aDest, na_tc);

	OlsrHashing(aDest, &hash);
	routing_hash = &olsr->routingtable[hash % HASHMASK];

	rt_entry* First_destination = NULL;


	for (destination = routing_hash->rt_back;
		destination != (rt_entry* ) routing_hash;
		destination = destination->rt_back)
	{
		if (destination->rt_hash != hash)
		{

			continue;
		}

		if (First_destination == NULL)
		{
			First_destination = destination;

			uiConfidentHopCount = First_destination->rt_entry_infos.rtu_metric;
			break;
		}
	}


	rt_entry* destination_tmp;
	
	
	//The remove indeed may not require, 
	//since this remove will be done at the begining of the routing table calculation
	//by function ProcessRoutingTableAccordingToConfidentCost
	if (bRemove)
	{

		destination = routing_hash->rt_forw;
		while (destination != (rt_entry *) routing_hash)
		{

			if (destination->rt_hash != hash)
			{

				destination = destination->rt_forw;

				//continue;
			}
			else
			{
				


				destination_tmp = destination;
				destination = destination->rt_forw;

				// deletes each routing entry from the table
				OlsrDeleteRoutingTable(destination_tmp);
			}
		}
	}

	//printf("ProcessRoutingTableAccordingToTC end!!!!!!!!!!!!!!!! \n");
	
	return uiConfidentHopCount;
}


destination_n* ProcessRoutingTableAccordingToRecentDeleteList(Node* node, BOOL * pbFurtherUpdateIsRequired)
{

	destination_n * list_destination_n = NULL;

	RoutingOlsr * olsr = (RoutingOlsr *) node->appData.olsr;

	tco_node_addr * tco_delete_list_tmp = olsr->recent_delete_list;			


	*pbFurtherUpdateIsRequired = FALSE;

	
	//if (tco_delete_list_tmp->nid == 10 && olsr->naRecentChangedAddressByTC == 15 && node->nodeId == 16)
	{

		//DebugBreak();
	}
	
	

	BOOL bCannotFindExchangeForAtLeastOneDest = FALSE;
	while (tco_delete_list_tmp != NULL)
	{

		UInt32 uiCurrentCost = MAX_COST;
		NodeAddress naCurrentRouter = 0; 

		NodeAddress naCurrentLastHop = 0;
		
		BOOL bReachTCFromTDNode = FALSE;

		//Only those route entry with olsr->naRecentChangedAddressByTC as lasthop and tco_delete_list_tmp->nid as the dest,
		//Or tco_delete_list_tmp->nid as the dest and olsr->naRecentChangedAddressByTC as lasthop need to be deleted
		//And these two cases can not exist at the same time, at least for single path routing ???

	
		tco_delete_list_tmp->bExchanged = FALSE;
		
		rt_entry* prte = QueryRoutingTableAccordingToNodeId(node, tco_delete_list_tmp->nid);

		rt_entry* prteTC = QueryRoutingTableAccordingToNodeId(node, olsr->naRecentChangedAddressByTC);
		

		rt_entry* prteToExchange = NULL;

		/*
		if (prte == NULL)
		{
			//May already been delete in former tc msgs
			//So assume all its related neighbors are already reasonably processed

			prte = QueryRoutingTableAccordingToNodeId(node, olsr->naRecentChangedAddressByTC);

			if (prte == NULL)
			{
				
				tco_delete_list_tmp = tco_delete_list_tmp->next;
				continue;
			}
			else
			{
				if (prte->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 == tco_delete_list_tmp->nid)
				{

					naCurrentRouter = prte->rt_router.interfaceAddr.ipv4;
					uiCurrentCost = prte->rt_metric;

					//delete the route entry here
					OlsrDeleteRoutingTable(prte);
				}
				else
				{

					tco_delete_list_tmp = tco_delete_list_tmp->next;
					continue;							
				}
								
			}
		}
		else
		*/
		
		
		//delete will not cause new dest to be reached, 
		
		//prte and prteTC will exist or non-exist at the same time???

		if (prte != NULL || prteTC != NULL)
		{
			if (prte != NULL  && prte->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 == olsr->naRecentChangedAddressByTC)
			{

				naCurrentRouter = prte->rt_router.interfaceAddr.ipv4;
				uiCurrentCost = prte->rt_metric;

				naCurrentLastHop = prte->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4;

				//delete the route entry here
				//OlsrRemoveList((olsr_qelem *)prte);
				//OlsrDeleteRoutingTable(prte);

				prteToExchange = prte;
			}
			else
			{

				if (prteTC != NULL && prteTC->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 == tco_delete_list_tmp->nid)
				{

					//
					naCurrentRouter = prteTC->rt_router.interfaceAddr.ipv4;
					uiCurrentCost = prteTC->rt_metric;

					naCurrentLastHop = prteTC->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4;
					
					//delete the route entry here
					//OlsrDeleteRoutingTable(prteTC);

					//OlsrRemoveList((olsr_qelem *)prteTC);

					prteToExchange = prteTC;

					bReachTCFromTDNode = TRUE;

				}
				else
				{
					tco_delete_list_tmp = tco_delete_list_tmp->next;
					continue;

				}

											
			}


			//



		}
		else
		{
			//
			return list_destination_n;
		}


		destination_list* topo_dest = NULL;
		destination_list* topo_dest2 = NULL;

		//rt_entry * pretmp = NULL;
		Address addrTmp;
		addrTmp.networkType = NETWORK_IPV4;


		if (bReachTCFromTDNode)
		{
			addrTmp.interfaceAddr.ipv4 = olsr->naRecentChangedAddressByTC;
		}
		else
		{
			addrTmp.interfaceAddr.ipv4 = tco_delete_list_tmp->nid;
		}


		

		topology_last_entry * t_last_sym = OlsrLookupLastTopologyTableSYM(node, addrTmp);
		if (t_last_sym != NULL)
		{

			topo_dest = t_last_sym->topology_list_of_destinations;


			rt_entry* prtetmpFormer = NULL;

			BOOL bSameCostFormer = FALSE;
			BOOL bCostPlusOneFormer = FALSE;
			
			BOOL bExistSameCostWithSameRouterFormer = FALSE;

			while (topo_dest != NULL)
			{
				
				Address addrReached = topo_dest->destination_node->topology_destination_dst;


				topo_dest = topo_dest->next;

				rt_entry* prteNearby = QueryRoutingTableAccordingToNodeId(node, addrReached.interfaceAddr.ipv4);
				if (prteNearby != NULL)
				{

					if (naCurrentLastHop != addrReached.interfaceAddr.ipv4)
					{

						//must satisfy prteNearby->rt_entry_infos.rtu_metric == uiCurrentCost or prteNearby->rt_entry_infos.rtu_metric + 1 = uiCurrentCost
						if (prteNearby->rt_entry_infos.rtu_metric + 1 == uiCurrentCost)
						{

							//bExist = TRUE;
							bSameCostFormer = TRUE;

							prtetmpFormer = prteNearby;

							if (prteNearby->rt_router.interfaceAddr.ipv4 == naCurrentRouter)
							{

								//same router
								bExistSameCostWithSameRouterFormer = TRUE;
								break;
							}
							else
							{

								//different router
								//topo_dest2 = topo_dest2->next;
								continue;
							}

						}


						/*
						if (!bSameCostFormer && prteNearby->rt_entry_infos.rtu_metric == uiCurrentCost)
						{


							bCostPlusOneFormer = TRUE;

							prtetmpFormer = prteNearby;


							//topo_dest2 = topo_dest2->next;
							continue;
						}
						*/

					}
				}
			}
			

			//tco_delete_list_tmp->bExchanged = bSameCostFormer || bCostPlusOneFormer;
			tco_delete_list_tmp->bExchanged = bSameCostFormer;

			if (tco_delete_list_tmp->bExchanged)
			{
				if (bSameCostFormer)
				{
					if (bExistSameCostWithSameRouterFormer)
					{
						
						//?????????????????????????????????
						
						prteToExchange->rt_entry_infos.rtu_lasthop = prtetmpFormer->rt_dst;
						
						
					}
					else
					{
						//?????????????????????????????????
						
						prteToExchange->rt_entry_infos.rtu_lasthop = prtetmpFormer->rt_dst;


						prteToExchange->rt_interface = prtetmpFormer->rt_interface;
						prteToExchange->rt_router = prtetmpFormer->rt_router;
						//prteNearby->rt_metric = (UInt16) (prtetmp->rt_metric + 1);
						

						prteToExchange->rt_entry_infos.rtu_DegreeWRTNode = prtetmpFormer->rt_entry_infos.rtu_DegreeWRTNode;
						prteToExchange->rt_entry_infos.rtu_DistanceWRTNode = prtetmpFormer->rt_entry_infos.rtu_DistanceWRTNode;
						prteToExchange->rt_entry_infos.related_neighbor = prtetmpFormer->rt_entry_infos.related_neighbor;
					}
				}
				/*
				else	//bCostPlusOne
				{

					
					prteToExchange->rt_entry_infos.rtu_lasthop = prtetmpFormer->rt_dst;


					prteToExchange->rt_interface = prtetmpFormer->rt_interface;
					prteToExchange->rt_router = prtetmpFormer->rt_router;
					prteToExchange->rt_metric = (UInt16) (prtetmpFormer->rt_metric + 1);
					

					prteToExchange->rt_entry_infos.rtu_DegreeWRTNode = prtetmpFormer->rt_entry_infos.rtu_DegreeWRTNode;
					prteToExchange->rt_entry_infos.rtu_DistanceWRTNode = prtetmpFormer->rt_entry_infos.rtu_DistanceWRTNode;
					prteToExchange->rt_entry_infos.related_neighbor = prtetmpFormer->rt_entry_infos.related_neighbor;
				}
				*/


				if (!bExistSameCostWithSameRouterFormer || !bSameCostFormer)
				{
					destination_n* list_destination_tmp;
					list_destination_tmp = (destination_n* )
						MEM_malloc(sizeof(destination_n));

					memset(
						list_destination_tmp,
						0,
						sizeof(destination_n));

					list_destination_tmp->destination = prteToExchange;
					list_destination_tmp->next = list_destination_n;
					list_destination_n = list_destination_tmp;
				}

				//process next one rather than use the next step exchange
				tco_delete_list_tmp = tco_delete_list_tmp->next;
				continue;


				//for bCostPlusOneFormer case, since it is possible that further exchange may result in better cost for 
				//some dest, since still need to further exchange
				/*
				if (!bCostPlusOneFormer)
				{

					tco_delete_list_tmp = tco_delete_list_tmp->next;
					continue;
				}
				*/
				
			}
			else
			{
				//

				if (prteToExchange != NULL)
				{


					OlsrDeleteRoutingTable(prteToExchange);
					//MEM_free(prteToExchange);
					prteToExchange = NULL;
				}

				
				//bCannotFindExchangeForAtLeastOneDest = TRUE;						
				//break;						
			}



			topo_dest = t_last_sym->topology_list_of_destinations;

			while (topo_dest != NULL)
			{
				Address addrReached = topo_dest->destination_node->topology_destination_dst;

				rt_entry* prteNearby = QueryRoutingTableAccordingToNodeId(node, addrReached.interfaceAddr.ipv4);
				if (prteNearby != NULL)
				{
										
					if (prteNearby->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 == addrTmp.interfaceAddr.ipv4)
					{

						//must satisfy prteNearby->rt_metric == prte->rt_metric + 1
						//search for exchange

						topology_last_entry * t_last_sym2 = OlsrLookupLastTopologyTableSYM(node, addrReached);
						if (t_last_sym2 != NULL)
						{
							topo_dest2 = t_last_sym2->topology_list_of_destinations;
							
							rt_entry* prtetmp = NULL;

							BOOL bSameCost = FALSE;
							BOOL bCostPlusOne = FALSE;
							BOOL bCostPlusTwo = FALSE;

							BOOL bExistSameCostWithSameRouter = FALSE;

							BOOL bExist = FALSE;

							while (topo_dest2 != NULL)
							{
							
								Address addrPotentailExchange = topo_dest2->destination_node->topology_destination_dst;

								//if (prteNearby2 != NULL)
								if (addrPotentailExchange.interfaceAddr.ipv4 != addrTmp.interfaceAddr.ipv4 
									//|| bCostPlusOneFormer && addrPotentailExchange.interfaceAddr.ipv4 == addrTmp.interfaceAddr.ipv4
									)
								{
									
									rt_entry* prteNearby2 = QueryRoutingTableAccordingToNodeId(node, addrPotentailExchange.interfaceAddr.ipv4);

									//if (addrPotentailExchange.interfaceAddr.ipv4 != tco_delete_list_tmp->nid)
									if (prteNearby2 != NULL)
									{

										/*
										if (prteNearby2->rt_metric < uiCurrentCost)
										{
											//impossible, or else current state of routing table does not satisfy the shortest cost requirement
										}
										*/
										

										if (prteNearby2->rt_metric == uiCurrentCost)
										{

											//exchange, for same or different route
										
											//bExist = TRUE;
											bSameCost = TRUE;

											prtetmp = prteNearby2;

											if (prteNearby2->rt_router.interfaceAddr.ipv4 == naCurrentRouter)
											{

												//same router
												bExistSameCostWithSameRouter = TRUE;
												break;
											}
											else
											{

												//different router
												topo_dest2 = topo_dest2->next;
												continue;
											}

										}


										/*
										//for the following two cases, exchange or not?
										if (!bSameCost && prteNearby2->rt_metric == uiCurrentCost + 1)
										{
											if (prteNearby2->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 != addrTmp.interfaceAddr.ipv4)
											{

												//bExist = TRUE;
												bCostPlusOne = TRUE;
											
												prtetmp = prteNearby2;


												topo_dest2 = topo_dest2->next;
												continue;
											}
										}

										if (!bSameCost && !bCostPlusOne && prteNearby2->rt_metric == uiCurrentCost + 2)
										{

											rt_entry* prteNearby3 = QueryRoutingTableAccordingToNodeId(node, prteNearby2->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4);

											if (prteNearby3 != NULL)
											{
												if (prteNearby3->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 != addrTmp.interfaceAddr.ipv4)
												{

													//bExist = TRUE;
													bCostPlusTwo = TRUE;
												
													prtetmp = prteNearby2;


													topo_dest2 = topo_dest2->next;
													continue;
												}
											}
										}
										*/

										

										/*
										if (prteNearby2->rt_metric > uiCurrentCost + 2)
										{
											//impossible, or else current state of routing table does not satisfy the shortest cost requirement
										}
										*/

									}
								}

								topo_dest2 = topo_dest2->next;				
							}


							//bExist =  bSameCost || bCostPlusOne || bCostPlusTwo;

							bExist =  bSameCost;
							if (bExist)
							{
								if (bSameCost)
								{
									if (bExistSameCostWithSameRouter)
									{
										
										//?????????????????????????????????
										/*
										if (_OLSR_MULTIPATH)
										{

											prteNearby->rt_entry_infos.oa_total_routes_count = prtetmp->rt_entry_infos.oa_total_routes_count;
											
											prteNearby->rt_entry_infos.oa_maximum_allowed_cost = prtetmp->rt_entry_infos.oa_maximum_allowed_cost;

											prteNearby->rt_entry_infos.oa_dWeightedDirectionDiffer = prtetmp->rt_entry_infos.oa_dWeightedDirectionDiffer;
										}
										*/

										//prteNearby->rt_interface = prtetmp->rt_interface;
										prteNearby->rt_entry_infos.rtu_lasthop = prtetmp->rt_dst;
										
										//prteNearby->rt_router = prtetmp->rt_router;
										//prteNearby->rt_metric = (UInt16) (prtetmp->rt_metric + 1);
										

										//prteNearby->rt_entry_infos.rtu_DegreeWRTNode = prtetmp->rt_entry_infos.rtu_DegreeWRTNode;
										//prteNearby->rt_entry_infos.rtu_DistanceWRTNode = prtetmp->rt_entry_infos.rtu_DistanceWRTNode;
										//prteNearby->rt_entry_infos.related_neighbor = prtetmp->rt_entry_infos.related_neighbor;
									}
									else
									{
										//?????????????????????????????????
										/*
										if (_OLSR_MULTIPATH)
										{

											prteNearby->rt_entry_infos.oa_total_routes_count = prtetmp->rt_entry_infos.oa_total_routes_count;
											
											prteNearby->rt_entry_infos.oa_maximum_allowed_cost = prtetmp->rt_entry_infos.oa_maximum_allowed_cost;

											prteNearby->rt_entry_infos.oa_dWeightedDirectionDiffer = prtetmp->rt_entry_infos.oa_dWeightedDirectionDiffer;
										}
										*/

										prteNearby->rt_entry_infos.rtu_lasthop = prtetmp->rt_dst;


										prteNearby->rt_interface = prtetmp->rt_interface;
										prteNearby->rt_router = prtetmp->rt_router;
										//prteNearby->rt_metric = (UInt16) (prtetmp->rt_metric + 1);
										

										prteNearby->rt_entry_infos.rtu_DegreeWRTNode = prtetmp->rt_entry_infos.rtu_DegreeWRTNode;
										prteNearby->rt_entry_infos.rtu_DistanceWRTNode = prtetmp->rt_entry_infos.rtu_DistanceWRTNode;
										prteNearby->rt_entry_infos.related_neighbor = prtetmp->rt_entry_infos.related_neighbor;
									}
								}
								else	//bCostPlusOne or bCostPlusTwo
								{

									//may not happen

									//?????????????????????????????????
									/*
									if (_OLSR_MULTIPATH)
									{

										prteNearby->rt_entry_infos.oa_total_routes_count = prtetmp->rt_entry_infos.oa_total_routes_count;
										
										prteNearby->rt_entry_infos.oa_maximum_allowed_cost = prtetmp->rt_entry_infos.oa_maximum_allowed_cost;

										prteNearby->rt_entry_infos.oa_dWeightedDirectionDiffer = prtetmp->rt_entry_infos.oa_dWeightedDirectionDiffer;
										}
									*/

									prteNearby->rt_entry_infos.rtu_lasthop = prtetmp->rt_dst;


									prteNearby->rt_interface = prtetmp->rt_interface;
									prteNearby->rt_router = prtetmp->rt_router;
									prteNearby->rt_metric = (UInt16) (prtetmp->rt_metric + 1);
									

									prteNearby->rt_entry_infos.rtu_DegreeWRTNode = prtetmp->rt_entry_infos.rtu_DegreeWRTNode;
									prteNearby->rt_entry_infos.rtu_DistanceWRTNode = prtetmp->rt_entry_infos.rtu_DistanceWRTNode;
									prteNearby->rt_entry_infos.related_neighbor = prtetmp->rt_entry_infos.related_neighbor;
								}


								if (!bExistSameCostWithSameRouter || !bSameCost)
								{
									destination_n* list_destination_tmp;
									list_destination_tmp = (destination_n* )
										MEM_malloc(sizeof(destination_n));

									memset(
										list_destination_tmp,
										0,
										sizeof(destination_n));

									list_destination_tmp->destination = prteNearby;
									list_destination_tmp->next = list_destination_n;
									list_destination_n = list_destination_tmp;
								}

							}
							else
							{

								bCannotFindExchangeForAtLeastOneDest = TRUE;

								/*
								if (prteToExchange != NULL)
								{


									MEM_free(prteToExchange);
									prteToExchange = NULL;
								}
								*/


								break;						
							}

						}
						
					}
					
				}
				else
				{
					//should be impossible, since if t_last_sym != NULL, then its neighbours should be already in routing table as well.
				}

				topo_dest = topo_dest->next;
			}

			if (bCannotFindExchangeForAtLeastOneDest)
			{

				break;
			}
		}
		else
		{
			//it is possible that this node should be delete has no neighbors
			//but this case can be handled by bFurtherUpdateIsRequired		

			if (prteToExchange != NULL)
			{


				OlsrDeleteRoutingTable(prteToExchange);
				//MEM_free(prteToExchange);
				prteToExchange = NULL;
			}
		}

		tco_delete_list_tmp = tco_delete_list_tmp->next;
	}

	
	if (bCannotFindExchangeForAtLeastOneDest)
	{

		//do Full Re-Calculation
		while (list_destination_n != NULL) 
		{

			destination_n* destination_n_1 = list_destination_n;
			list_destination_n = list_destination_n->next;
			MEM_free(destination_n_1);
		}

		list_destination_n = NULL;

		*pbFurtherUpdateIsRequired = TRUE;

		//do not remove the route entry here, since assume the further update will clear all and re-calculate


		//Add neighbor and 2HopNeighbor for full re-calculation,
		//which is done outside this function
		
	}
	else
	{
		//do update for exchange
		
	}

	return list_destination_n;
}


BOOL FindLastExchange(Node* node, rt_entry* reTBExchanged, tco_node_addr ** ptna_source_set, UInt32 * puiLookupCntForRE)
{


	BOOL bExchangeFound = FALSE;

	UInt32 uiLookupCnt = 0;

	topology_last_entry * t_last_sym = OlsrLookupLastTopologyTableSYM(node, reTBExchanged->rt_dst);
	if (t_last_sym != NULL)
	{
		destination_list* topo_dest = NULL;

		topo_dest = t_last_sym->topology_list_of_destinations;

		//rt_entry* prtetmp = NULL;

		

		while (topo_dest != NULL)
		{

			Address addrReached = topo_dest->destination_node->topology_destination_dst;


			topo_dest = topo_dest->next;

					
			if (exist_in_tco_node_addr_set(ptna_source_set, addrReached.interfaceAddr.ipv4))
			{
				
				//exchange the last hop only
				reTBExchanged->rt_entry_infos.rtu_lasthop = addrReached;


				bExchangeFound = TRUE;
				break;
			}	

		}


	}
		

	


	if (_TEST_TIME_COMPLEXITY && puiLookupCntForRE)
	{
		*puiLookupCntForRE += uiLookupCnt;
	}


	return bExchangeFound;

}



BOOL FindRouteExchangeV2(Node* node, rt_entry* reTBExchanged, BOOL bIncludeOldLastHop, UInt32 * puiLookupCntForRE, BOOL bRequireSameRouter, tco_node_addr ** ptna_set, BOOL * pbPossibleToFound)
{

	BOOL bExchangeFound = FALSE;

	UInt32 uiLookupCnt = 0;

	topology_last_entry * t_last_sym = OlsrLookupLastTopologyTableSYM(node, reTBExchanged->rt_dst);
	if (t_last_sym != NULL)
	{
		destination_list* topo_dest = NULL;

		topo_dest = t_last_sym->topology_list_of_destinations;

		rt_entry* prtetmp = NULL;

		BOOL bSameCost = FALSE;
		BOOL bCostPlusOne = FALSE;
		BOOL bCostPlusTwo = FALSE;

		BOOL bExistSameCostWithSameRouter = FALSE;

		BOOL bExist = FALSE;

		while (topo_dest != NULL)
		{

			Address addrReached = topo_dest->destination_node->topology_destination_dst;


			topo_dest = topo_dest->next;

			rt_entry* prteNearby = QueryRoutingTableAccordingToNodeId(node, addrReached.interfaceAddr.ipv4);
			if (_TEST_TIME_COMPLEXITY && puiLookupCntForRE)
			{
				uiLookupCnt++;
			}

			if (!bRequireSameRouter && prteNearby != NULL 
				|| bRequireSameRouter && prteNearby != NULL && (prteNearby->rt_router.interfaceAddr.ipv4 == reTBExchanged->rt_router.interfaceAddr.ipv4))
			{

				if (!bIncludeOldLastHop && reTBExchanged->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 != addrReached.interfaceAddr.ipv4
					|| bIncludeOldLastHop)
				{

					
					if (ptna_set != NULL)
					{
						bool bIsAlsoDisconnectedEntry = exist_in_tco_node_addr_set(ptna_set, addrReached.interfaceAddr.ipv4);
						if (bIsAlsoDisconnectedEntry)
						{
							if (pbPossibleToFound)
							{
								*pbPossibleToFound = TRUE;
							}

							continue;
						}
					}

					//must satisfy prteNearby->rt_entry_infos.rtu_metric == uiCurrentCost or prteNearby->rt_entry_infos.rtu_metric + 1 = uiCurrentCost
					if (prteNearby->rt_metric == reTBExchanged->rt_metric - 1)
					{

						bSameCost = TRUE;

						prtetmp = prteNearby;

						if (prteNearby->rt_router.interfaceAddr.ipv4 == reTBExchanged->rt_router.interfaceAddr.ipv4)
						{

							//same router
							bExistSameCostWithSameRouter = TRUE;
							break;
						}
						else
						{

							//different router

							continue;
						}

					}


					if (!bSameCost && prteNearby->rt_metric == reTBExchanged->rt_metric 
						//comment reason: if this indirect link does exist, then it is ok, 
						//since the disconnect of direct link does not mean the disconnect of the indirect link
						//&& reTBExchanged->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 != prteNearby->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4
						)
					{


						bCostPlusOne = TRUE;

						prtetmp = prteNearby;

						continue;
					}


					if (!bSameCost && !bCostPlusOne && prteNearby->rt_metric == reTBExchanged->rt_metric + 1
						&& prteNearby->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 != reTBExchanged->rt_entry_infos.rtu_dst.interfaceAddr.ipv4)
					{

						//comment reason: if this indirect link does exist, then it is ok, 
						//since the disconnect of direct link does not mean the disconnect of the indirect link
						//rt_entry* prteNearby2 = QueryRoutingTableAccordingToNodeId(node, prteNearby->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4);

						//if (prteNearby2 != NULL)
						{
							//if (prteNearby2->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 != reTBExchanged->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4)
							{


								bCostPlusTwo = TRUE;

								prtetmp = prteNearby;


								continue;
							}
						}
					}

				}
				else
				{
					//will not happen, since it should already be deleted
				}

			}

		}



		bExchangeFound =  bSameCost || bCostPlusOne || bCostPlusTwo;


		if (bExchangeFound)
		{
			if (bSameCost)
			{

				reTBExchanged->rt_entry_infos.bCostChanged = FALSE;
				reTBExchanged->rt_entry_infos.uiCostChg = 0;

				if (bExistSameCostWithSameRouter)
				{


					reTBExchanged->rt_entry_infos.rtu_lasthop = prtetmp->rt_dst;


				}
				else		//route changed
				{

					reTBExchanged->rt_entry_infos.rtu_lasthop = prtetmp->rt_dst;


					reTBExchanged->rt_interface = prtetmp->rt_interface;
					reTBExchanged->rt_router = prtetmp->rt_router;


					reTBExchanged->rt_entry_infos.rtu_DegreeWRTNode = prtetmp->rt_entry_infos.rtu_DegreeWRTNode;
					reTBExchanged->rt_entry_infos.rtu_DistanceWRTNode = prtetmp->rt_entry_infos.rtu_DistanceWRTNode;
					reTBExchanged->rt_entry_infos.related_neighbor = prtetmp->rt_entry_infos.related_neighbor;
				}
			}
			else	//bCostPlusOne or bCostPlusTwo
			{


				if (bCostPlusOne)
				{
					reTBExchanged->rt_entry_infos.uiCostChg = 1;
				}
				else
				{
					reTBExchanged->rt_entry_infos.uiCostChg = 2;
				}

				reTBExchanged->rt_entry_infos.bCostChanged = TRUE;

				reTBExchanged->rt_entry_infos.rtu_lasthop = prtetmp->rt_dst;


				reTBExchanged->rt_interface = prtetmp->rt_interface;
				reTBExchanged->rt_router = prtetmp->rt_router;

				reTBExchanged->rt_metric = (UInt16) (prtetmp->rt_metric + 1);


				reTBExchanged->rt_entry_infos.rtu_DegreeWRTNode = prtetmp->rt_entry_infos.rtu_DegreeWRTNode;
				reTBExchanged->rt_entry_infos.rtu_DistanceWRTNode = prtetmp->rt_entry_infos.rtu_DistanceWRTNode;
				reTBExchanged->rt_entry_infos.related_neighbor = prtetmp->rt_entry_infos.related_neighbor;
			}


			if (bExistSameCostWithSameRouter)
			{

				reTBExchanged->rt_entry_infos.bDescendentRequireFurtherUpdate = FALSE;
			}
			else
			{

				reTBExchanged->rt_entry_infos.bDescendentRequireFurtherUpdate = TRUE;
			}


		}
		else
		{


			//need to delete


		}

	}
	else
	{
		//need to delete

	}


	if (_TEST_TIME_COMPLEXITY && puiLookupCntForRE)
	{
		*puiLookupCntForRE += uiLookupCnt;
	}


	return bExchangeFound;
}


BOOL BelongsToItsChildren(destination_n * pChildren, NodeAddress naIPtoCheck)
{

	BOOL bIsAChild = FALSE;

	destination_n * pd_tmp = NULL;
	if (pChildren != NULL)
	{

		pd_tmp = pChildren;
		while (pd_tmp != NULL)
		{

			if (pd_tmp->destination->rt_entry_infos.rtu_dst.interfaceAddr.ipv4 == naIPtoCheck)
			{

				bIsAChild = TRUE;
				break;
			}

			pd_tmp = pd_tmp->next;
		}
	}

	return bIsAChild;
}


void AddToChildrenList(destination_n ** pChildren, rt_entry * prteChild)
{

	destination_n* list_destination_tmp;
	list_destination_tmp = (destination_n* )
		MEM_malloc(sizeof(destination_n));

	memset(list_destination_tmp, 0, sizeof(destination_n));

	//list_destination_tmp->destination = preExisting;

	
	list_destination_tmp->destination = prteChild;

	list_destination_tmp->next = *pChildren;
	*pChildren = list_destination_tmp;
}


void ClearChildrenList(destination_n * pChildren)
{

	destination_n * pd_tmp = NULL;
	if (pChildren != NULL)
	{

		pd_tmp = pChildren;
		while (pd_tmp != NULL)
		{
			destination_n* list_destination_tmp = pd_tmp;
			

			pd_tmp = pd_tmp->next;

			MEM_free(list_destination_tmp);
		}
	}

}



BOOL FindRouteExchangeV22(Node* node, destination_n * dTBExchanged, rt_entry* reTBExchanged, BOOL bIncludeOldLastHop, rt_entry* reOldLast, UInt32 * puiLookupCntForRE, BOOL bRequireSameRouter, tco_node_addr ** ptna_set, tco_node_addr ** ptna_set2, tco_node_addr ** ptna_set_fore, tco_node_addr ** ptna_set_fore2, BOOL * pbPossibleToFound)
{

	BOOL bExchangeFound = FALSE;

	UInt32 uiLookupCnt = 0;

	//rt_entry* reTBExchanged = dTBExchanged->destination;

	topology_last_entry * t_last_sym = OlsrLookupLastTopologyTableSYM(node, reTBExchanged->rt_dst);
	if (t_last_sym != NULL)
	{
		destination_list* topo_dest = NULL;

		topo_dest = t_last_sym->topology_list_of_destinations;


		BOOL bOldLastMaybePrefered = FALSE;
		//int iCostForOldLastPreferToApply = reOldLast->rt_metric;
		if (bIncludeOldLastHop)
		{

			if (reOldLast != NULL)
			{

				if (g_iToAchieveSameRoute == 1)
				{

				}
				else
				{
					bOldLastMaybePrefered = TRUE;
				}
			
			}
		}


		rt_entry* prtetmp = NULL;

		BOOL bSameCost = FALSE;
		BOOL bCostPlusOne = FALSE;
		BOOL bCostPlusTwo = FALSE;

		BOOL bExistSameCostWithSameRouter = FALSE;

		BOOL bExist = FALSE;

		while (topo_dest != NULL)
		{

			Address addrReached = topo_dest->destination_node->topology_destination_dst;


			topo_dest = topo_dest->next;

			if (dTBExchanged != NULL)
			{
				if (dTBExchanged->bChildrenDetermined)
				{
					//check if this reached one belong to its children, to reduce the execution of QueryRoutingTableAccordingToNodeId
					if (BelongsToItsChildren(dTBExchanged->children, addrReached.interfaceAddr.ipv4))
					{
						continue;
					}
				}
			}


			if (ptna_set != NULL)
			{
				bool bIsAlsoDisconnectedEntry = exist_in_tco_node_addr_set(ptna_set, addrReached.interfaceAddr.ipv4);
				if (bIsAlsoDisconnectedEntry)
				{

					if (pbPossibleToFound)
					{
						*pbPossibleToFound = TRUE;
					}

					continue;
				}
			}


			if (ptna_set2 != NULL)
			{
				bool bIsAlsoDisconnectedEntry = exist_in_tco_node_addr_set(ptna_set2, addrReached.interfaceAddr.ipv4);
				if (bIsAlsoDisconnectedEntry)
				{

					if (pbPossibleToFound)
					{
						*pbPossibleToFound = TRUE;
					}

					continue;
				}
			}

			rt_entry* prteNearby = QueryRoutingTableAccordingToNodeId(node, addrReached.interfaceAddr.ipv4);


			if (dTBExchanged != NULL && prteNearby != NULL)
			{
				if (!dTBExchanged->bChildrenDetermined)
				{
					if (prteNearby->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 == reTBExchanged->rt_entry_infos.rtu_dst.interfaceAddr.ipv4)
					{

						//is a child, add to children list
						AddToChildrenList(&(dTBExchanged->children), prteNearby);

						continue;
					}
				}
			}



			if (_TEST_TIME_COMPLEXITY && puiLookupCntForRE)
			{
				uiLookupCnt++;
			}

			if (!bRequireSameRouter && prteNearby != NULL 
				|| bRequireSameRouter && prteNearby != NULL && (prteNearby->rt_router.interfaceAddr.ipv4 == reTBExchanged->rt_router.interfaceAddr.ipv4))
			{

				if (!bIncludeOldLastHop && reTBExchanged->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 != addrReached.interfaceAddr.ipv4
					|| bIncludeOldLastHop)
				{


					//must satisfy prteNearby->rt_entry_infos.rtu_metric == uiCurrentCost or prteNearby->rt_entry_infos.rtu_metric + 1 = uiCurrentCost
					if (prteNearby->rt_metric == reTBExchanged->rt_metric - 1)
					{

						if (g_iToAchieveSameRoute == 1)
						{

							if (bSameCost)
							{
								if (PreferredRouteForNew(prteNearby->rt_router.interfaceAddr.ipv4, prtetmp->rt_router.interfaceAddr.ipv4))
								{
									prtetmp = prteNearby;
								}
							}
							else
							{
								prtetmp = prteNearby;
							}

							bSameCost = TRUE;

							continue;

						}
						else
						{
							bSameCost = TRUE;

							prtetmp = prteNearby;

							if (prteNearby->rt_router.interfaceAddr.ipv4 == reTBExchanged->rt_router.interfaceAddr.ipv4)
							{

								//same router
								bExistSameCostWithSameRouter = TRUE;
								break;
							}
							else
							{

								//different router

								continue;
							}
						}

					}


					//just do not consider any cost change


					
					if (!bSameCost && prteNearby->rt_metric == reTBExchanged->rt_metric 
						//comment reason: if this indirect link does exist, then it is ok, 
						//since the disconnect of direct link does not mean the disconnect of the indirect link
						//&& reTBExchanged->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 != prteNearby->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4
						)
					{


						if (bOldLastMaybePrefered && reOldLast->rt_metric == prteNearby->rt_metric)
						{

							prtetmp = reOldLast;
						}
						else
						{

							if (g_iToAchieveSameRoute == 1)
							{


								if (ptna_set_fore != NULL)
								{
									bool bIsAlsoDisconnectedEntry = exist_in_tco_node_addr_set(ptna_set_fore, prteNearby->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4);
									if (bIsAlsoDisconnectedEntry)
									{

										if (pbPossibleToFound)
										{
											*pbPossibleToFound = TRUE;
										}

										continue;
									}
								}


								if (ptna_set_fore2 != NULL)
								{
									bool bIsAlsoDisconnectedEntry = exist_in_tco_node_addr_set(ptna_set_fore2, prteNearby->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4);
									if (bIsAlsoDisconnectedEntry)
									{

										if (pbPossibleToFound)
										{
											*pbPossibleToFound = TRUE;
										}

										continue;
									}
								}



								if (bCostPlusOne)
								{
									if (PreferredRouteForNew(prteNearby->rt_entry_infos.rtu_router.interfaceAddr.ipv4, prtetmp->rt_entry_infos.rtu_router.interfaceAddr.ipv4))
									{
										prtetmp = prteNearby;
									}
								}
								else
								{
									prtetmp = prteNearby;
								}

							}
							else
							{
								prtetmp = prteNearby;
							}
						}

						bCostPlusOne = TRUE;


						continue;
					}


					
					if (!bSameCost && !bCostPlusOne && prteNearby->rt_metric == reTBExchanged->rt_metric + 1
						&& prteNearby->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 != reTBExchanged->rt_entry_infos.rtu_dst.interfaceAddr.ipv4)
					{


						if (ptna_set_fore != NULL)
						{
							bool bIsAlsoDisconnectedEntry = exist_in_tco_node_addr_set(ptna_set_fore, prteNearby->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4);
							if (bIsAlsoDisconnectedEntry)
							{

								if (pbPossibleToFound)
								{
									*pbPossibleToFound = TRUE;
								}

								continue;
							}
						}


						if (ptna_set_fore2 != NULL)
						{
							bool bIsAlsoDisconnectedEntry = exist_in_tco_node_addr_set(ptna_set_fore2, prteNearby->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4);
							if (bIsAlsoDisconnectedEntry)
							{

								if (pbPossibleToFound)
								{
									*pbPossibleToFound = TRUE;
								}

								continue;
							}
						}



						//comment reason: if this indirect link does exist, then it is ok, 
						//since the disconnect of direct link does not mean the disconnect of the indirect link
						//rt_entry* prteNearby2 = QueryRoutingTableAccordingToNodeId(node, prteNearby->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4);

						//if (prteNearby2 != NULL)
						{
							//if (prteNearby2->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 != reTBExchanged->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4)
							{

								if (bOldLastMaybePrefered && reOldLast->rt_metric == prteNearby->rt_metric)
								{

									prtetmp = reOldLast;


								}
								else
								{
									if (g_iToAchieveSameRoute == 1)
									{

										if (bCostPlusTwo)
										{
											if (PreferredRouteForNew(prteNearby->rt_entry_infos.rtu_router.interfaceAddr.ipv4, prtetmp->rt_entry_infos.rtu_router.interfaceAddr.ipv4))
											{
												prtetmp = prteNearby;
											}
										}
										else
										{
											prtetmp = prteNearby;
										}

									}
									else
									{
										prtetmp = prteNearby;
									}
								}

								bCostPlusTwo = TRUE;


								continue;
							}
						}
					}
					

				}
				else
				{
					//will not happen, since it should already be deleted
				}

			}

		}


		if (dTBExchanged != NULL)
		{

			dTBExchanged->bChildrenDetermined = TRUE;
		}


		bExchangeFound =  bSameCost || bCostPlusOne || bCostPlusTwo;


		if (bExchangeFound)
		{
			if (bSameCost)
			{

				reTBExchanged->rt_entry_infos.bCostChanged = FALSE;

				reTBExchanged->rt_entry_infos.uiCostChg = 0;

				

				if (g_iToAchieveSameRoute == 1)
				{

					if (prtetmp->rt_router.interfaceAddr.ipv4 == reTBExchanged->rt_router.interfaceAddr.ipv4)
					{

						bExistSameCostWithSameRouter = TRUE;
					}						
				}

				if (bExistSameCostWithSameRouter)
				{


					reTBExchanged->rt_entry_infos.rtu_lasthop = prtetmp->rt_dst;

					if (dTBExchanged != NULL)
					{


						ClearChildrenList(dTBExchanged->children);
					}

				}
				else
				{

					reTBExchanged->rt_entry_infos.rtu_lasthop = prtetmp->rt_dst;


					reTBExchanged->rt_interface = prtetmp->rt_interface;
					reTBExchanged->rt_router = prtetmp->rt_router;


					if (_OLSR_MULTIPATH)
					{

						reTBExchanged->rt_entry_infos.rtu_DegreeWRTNode = prtetmp->rt_entry_infos.rtu_DegreeWRTNode;
						reTBExchanged->rt_entry_infos.rtu_DistanceWRTNode = prtetmp->rt_entry_infos.rtu_DistanceWRTNode;
						reTBExchanged->rt_entry_infos.related_neighbor = prtetmp->rt_entry_infos.related_neighbor;
					}

				}
			}			
			else	//bCostPlusOne or bCostPlusTwo
			{


				if (bCostPlusOne)
				{
					reTBExchanged->rt_entry_infos.uiCostChg = 1;
				}
				else
				{
					reTBExchanged->rt_entry_infos.uiCostChg = 2;
				}

				reTBExchanged->rt_entry_infos.bCostChanged = TRUE;

				reTBExchanged->rt_entry_infos.rtu_lasthop = prtetmp->rt_dst;


				reTBExchanged->rt_interface = prtetmp->rt_interface;
				reTBExchanged->rt_router = prtetmp->rt_router;

				reTBExchanged->rt_metric = (UInt16) (prtetmp->rt_metric + 1);

				if (_OLSR_MULTIPATH)
				{

					reTBExchanged->rt_entry_infos.rtu_DegreeWRTNode = prtetmp->rt_entry_infos.rtu_DegreeWRTNode;
					reTBExchanged->rt_entry_infos.rtu_DistanceWRTNode = prtetmp->rt_entry_infos.rtu_DistanceWRTNode;
					reTBExchanged->rt_entry_infos.related_neighbor = prtetmp->rt_entry_infos.related_neighbor;
				}

			}
			


			if (bExistSameCostWithSameRouter)
			{

				reTBExchanged->rt_entry_infos.bDescendentRequireFurtherUpdate = FALSE;
			}
			else
			{

				reTBExchanged->rt_entry_infos.bDescendentRequireFurtherUpdate = TRUE;
			}


		}
		else
		{

			//need to delete
		}

	}
	else
	{

		//need to delete
	}


	if (_TEST_TIME_COMPLEXITY && puiLookupCntForRE)
	{
		*puiLookupCntForRE += uiLookupCnt;
	}


	return bExchangeFound;
}



BOOL FindRouteExchangeV21(Node* node, destination_n * dTBExchanged, rt_entry* reTBExchanged, BOOL bIncludeOldLastHop, rt_entry* reOldLast, UInt32 * puiLookupCntForRE, BOOL bRequireSameRouter, tco_node_addr ** ptna_set, tco_node_addr ** ptna_set2, tco_node_addr ** ptna_set3,  
						  tco_node_addr ** ptna_set_fore, tco_node_addr ** ptna_set_fore2, BOOL * pbPossibleToFound)
{

	BOOL bExchangeFound = FALSE;

	UInt32 uiLookupCnt = 0;

	//rt_entry* reTBExchanged = dTBExchanged->destination;

	topology_last_entry * t_last_sym = OlsrLookupLastTopologyTableSYM(node, reTBExchanged->rt_dst);
	if (t_last_sym != NULL)
	{
		destination_list* topo_dest = NULL;

		topo_dest = t_last_sym->topology_list_of_destinations;


		BOOL bOldLastCanbePrefered = FALSE;
		if (bIncludeOldLastHop)
		{

			if (reOldLast != NULL)
			{
				//prefer the old last hop
				if (reOldLast->rt_metric == reTBExchanged->rt_metric)
				{
					if (g_iToAchieveSameRoute == 1)
					{

					}
					else
					{
						bOldLastCanbePrefered = TRUE;
					}
										
				}
			}
		}


		rt_entry* prtetmp = NULL;

		BOOL bSameCost = FALSE;
		BOOL bCostPlusOne = FALSE;
		//BOOL bCostPlusTwo = FALSE;

		BOOL bExistSameCostWithSameRouter = FALSE;

		BOOL bExist = FALSE;

		while (topo_dest != NULL)
		{

			Address addrReached = topo_dest->destination_node->topology_destination_dst;


			topo_dest = topo_dest->next;

			if (dTBExchanged != NULL)
			{
				if (dTBExchanged->bChildrenDetermined)
				{
					//check if this reached one belong to its children, to reduce the execution of QueryRoutingTableAccordingToNodeId
					if (BelongsToItsChildren(dTBExchanged->children, addrReached.interfaceAddr.ipv4))
					{
						continue;
					}
				}
			}			
			
			
			if (ptna_set != NULL)
			{
				bool bIsAlsoDisconnectedEntry = exist_in_tco_node_addr_set(ptna_set, addrReached.interfaceAddr.ipv4);
				if (bIsAlsoDisconnectedEntry)
				{

					if (pbPossibleToFound)
					{
						*pbPossibleToFound = TRUE;
					}

					continue;
				}
			}

			if (ptna_set2 != NULL)
			{
				bool bIsAlsoDisconnectedEntry = exist_in_tco_node_addr_set(ptna_set2, addrReached.interfaceAddr.ipv4);
				if (bIsAlsoDisconnectedEntry)
				{

					if (pbPossibleToFound)
					{
						*pbPossibleToFound = TRUE;
					}

					continue;
				}
			}


			if (ptna_set3 != NULL)
			{
				bool bIsAlsoDisconnectedEntry = exist_in_tco_node_addr_set(ptna_set3, addrReached.interfaceAddr.ipv4);
				if (bIsAlsoDisconnectedEntry)
				{

					if (pbPossibleToFound)
					{
						*pbPossibleToFound = TRUE;
					}

					continue;
				}
			}


			rt_entry* prteNearby = QueryRoutingTableAccordingToNodeId(node, addrReached.interfaceAddr.ipv4);


			if (dTBExchanged != NULL && prteNearby != NULL)
			{
				if (!dTBExchanged->bChildrenDetermined)
				{
					if (prteNearby->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 == reTBExchanged->rt_entry_infos.rtu_dst.interfaceAddr.ipv4)
					{

						//is a child, add to children list
						AddToChildrenList(&(dTBExchanged->children), prteNearby);

						continue;
					}
				}
			}


			if (_TEST_TIME_COMPLEXITY && puiLookupCntForRE)
			{
				uiLookupCnt++;
			}

			if (!bRequireSameRouter && prteNearby != NULL 
				|| bRequireSameRouter && prteNearby != NULL && (prteNearby->rt_router.interfaceAddr.ipv4 == reTBExchanged->rt_router.interfaceAddr.ipv4))
			{

				if (!bIncludeOldLastHop && reTBExchanged->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 != addrReached.interfaceAddr.ipv4
					|| bIncludeOldLastHop)
				{


					

					//must satisfy prteNearby->rt_entry_infos.rtu_metric == uiCurrentCost or prteNearby->rt_entry_infos.rtu_metric + 1 = uiCurrentCost
					if (prteNearby->rt_metric == reTBExchanged->rt_metric - 1)
					{

						if (g_iToAchieveSameRoute == 1)
						{

							if (bSameCost)
							{
								if (PreferredRouteForNew(prteNearby->rt_router.interfaceAddr.ipv4, prtetmp->rt_router.interfaceAddr.ipv4))
								{
									prtetmp = prteNearby;
								}
							}
							else
							{
								prtetmp = prteNearby;
							}

							bSameCost = TRUE;

							continue;

						}
						else
						{

							bSameCost = TRUE;

							prtetmp = prteNearby;

							if (prteNearby->rt_router.interfaceAddr.ipv4 == reTBExchanged->rt_router.interfaceAddr.ipv4)
							{

								//same router
								bExistSameCostWithSameRouter = TRUE;


								break;

							}
							else
							{

								//different router

								continue;
							}

						}

					}

					//just do not consider any cost change


					
					if (!bSameCost && prteNearby->rt_metric == reTBExchanged->rt_metric 
						//comment reason: if this indirect link does exist, then it is ok, 
						//since the disconnect of direct link does not mean the disconnect of the indirect link
						//&& reTBExchanged->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 != prteNearby->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4
						)
					{

						
						if (bIncludeOldLastHop && bOldLastCanbePrefered)
						{

							prtetmp = reOldLast;
							
						}
						else
						{

							if (g_iToAchieveSameRoute == 1)
							{
								

								if (ptna_set_fore != NULL)
								{
									bool bIsAlsoDisconnectedEntry = exist_in_tco_node_addr_set(ptna_set_fore, prteNearby->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4);
									if (bIsAlsoDisconnectedEntry)
									{

										if (pbPossibleToFound)
										{
											*pbPossibleToFound = TRUE;
										}

										continue;
									}
								}

								if (ptna_set_fore2 != NULL)
								{
									bool bIsAlsoDisconnectedEntry = exist_in_tco_node_addr_set(ptna_set_fore2, prteNearby->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4);
									if (bIsAlsoDisconnectedEntry)
									{

										if (pbPossibleToFound)
										{
											*pbPossibleToFound = TRUE;
										}

										continue;
									}
								}


								

								if (bCostPlusOne)
								{
									if (PreferredRouteForNew(prteNearby->rt_entry_infos.rtu_router.interfaceAddr.ipv4, prtetmp->rt_entry_infos.rtu_router.interfaceAddr.ipv4))
									{
										prtetmp = prteNearby;
									}
								}
								else
								{
									prtetmp = prteNearby;
								}

							}
							else
							{
								prtetmp = prteNearby;
							}


							
						}

						bCostPlusOne = TRUE;
						

						continue;
					}


					/*
					if (!bSameCost && !bCostPlusOne && prteNearby->rt_metric == reTBExchanged->rt_metric + 1
						&& prteNearby->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 != reTBExchanged->rt_entry_infos.rtu_dst.interfaceAddr.ipv4)
					{

						//comment reason: if this indirect link does exist, then it is ok, 
						//since the disconnect of direct link does not mean the disconnect of the indirect link
						//rt_entry* prteNearby2 = QueryRoutingTableAccordingToNodeId(node, prteNearby->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4);

						//if (prteNearby2 != NULL)
						{
							//if (prteNearby2->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 != reTBExchanged->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4)
							{


								bCostPlusTwo = TRUE;

								prtetmp = prteNearby;


								continue;
							}
						}
					}
					*/

				}
				else
				{
					//will not happen, since it should already be deleted
				}

			}

		}


		if (dTBExchanged != NULL)
		{
			
			dTBExchanged->bChildrenDetermined = TRUE;
		}


		bExchangeFound =  bSameCost || bCostPlusOne;//|| bCostPlusTwo;


		if (bExchangeFound)
		{
			if (bSameCost)
			{

				reTBExchanged->rt_entry_infos.bCostChanged = FALSE;

				reTBExchanged->rt_entry_infos.uiCostChg = 0;


				if (g_iToAchieveSameRoute == 1)
				{

					if (prtetmp->rt_router.interfaceAddr.ipv4 == reTBExchanged->rt_router.interfaceAddr.ipv4)
					{

						bExistSameCostWithSameRouter = TRUE;
					}						
				}
				

				if (bExistSameCostWithSameRouter)
				{

					reTBExchanged->rt_entry_infos.rtu_lasthop = prtetmp->rt_dst;

					if (dTBExchanged != NULL)
					{

						//dTBExchanged->bChildrenDetermined = TRUE;
						ClearChildrenList(dTBExchanged->children);

					}
				}
				else
				{

					reTBExchanged->rt_entry_infos.rtu_lasthop = prtetmp->rt_dst;


					reTBExchanged->rt_interface = prtetmp->rt_interface;
					reTBExchanged->rt_router = prtetmp->rt_router;


					if (_OLSR_MULTIPATH)
					{

						reTBExchanged->rt_entry_infos.rtu_DegreeWRTNode = prtetmp->rt_entry_infos.rtu_DegreeWRTNode;
						reTBExchanged->rt_entry_infos.rtu_DistanceWRTNode = prtetmp->rt_entry_infos.rtu_DistanceWRTNode;
						reTBExchanged->rt_entry_infos.related_neighbor = prtetmp->rt_entry_infos.related_neighbor;
					}
				}
			}			
			else	//bCostPlusOne 
			{

				reTBExchanged->rt_entry_infos.uiCostChg = 1;
				


				reTBExchanged->rt_entry_infos.bCostChanged = TRUE;

				reTBExchanged->rt_entry_infos.rtu_lasthop = prtetmp->rt_dst;


				reTBExchanged->rt_interface = prtetmp->rt_interface;
				reTBExchanged->rt_router = prtetmp->rt_router;

				reTBExchanged->rt_metric = (UInt16) (prtetmp->rt_metric + 1);


				if (_OLSR_MULTIPATH)
				{

					reTBExchanged->rt_entry_infos.rtu_DegreeWRTNode = prtetmp->rt_entry_infos.rtu_DegreeWRTNode;
					reTBExchanged->rt_entry_infos.rtu_DistanceWRTNode = prtetmp->rt_entry_infos.rtu_DistanceWRTNode;
					reTBExchanged->rt_entry_infos.related_neighbor = prtetmp->rt_entry_infos.related_neighbor;
				}
			}
			


			if (bExistSameCostWithSameRouter)
			{

				reTBExchanged->rt_entry_infos.bDescendentRequireFurtherUpdate = FALSE;
			}
			else
			{

				reTBExchanged->rt_entry_infos.bDescendentRequireFurtherUpdate = TRUE;
			}


		}
		else
		{


			//need to delete


		}

	}
	else
	{
		//need to delete

	}


	if (_TEST_TIME_COMPLEXITY && puiLookupCntForRE)
	{
		*puiLookupCntForRE += uiLookupCnt;
	}


	return bExchangeFound;
}


BOOL FindRouteExchangeV20(Node* node, destination_n * dTBExchanged, rt_entry* reTBExchanged, BOOL bIncludeOldLastHop, UInt32 * puiLookupCntForRE, BOOL bRequireSameRouter, tco_node_addr ** ptna_set, tco_node_addr ** ptna_set2, BOOL * pbPossibleToFound)
{

	BOOL bExchangeFound = FALSE;

	UInt32 uiLookupCnt = 0;

	//rt_entry* reTBExchanged = dTBExchanged->destination;

	topology_last_entry * t_last_sym = OlsrLookupLastTopologyTableSYM(node, reTBExchanged->rt_dst);
	if (t_last_sym != NULL)
	{
		destination_list* topo_dest = NULL;

		topo_dest = t_last_sym->topology_list_of_destinations;

		rt_entry* prtetmp = NULL;

		BOOL bSameCost = FALSE;
		//BOOL bCostPlusOne = FALSE;
		//BOOL bCostPlusTwo = FALSE;

		BOOL bExistSameCostWithSameRouter = FALSE;

		BOOL bExist = FALSE;

		while (topo_dest != NULL)
		{

			Address addrReached = topo_dest->destination_node->topology_destination_dst;


			topo_dest = topo_dest->next;

			if (dTBExchanged != NULL)
			{
				if (dTBExchanged->bChildrenDetermined)
				{
					//check if this reached one belong to its children, to reduce the execution of QueryRoutingTableAccordingToNodeId
					if (BelongsToItsChildren(dTBExchanged->children, addrReached.interfaceAddr.ipv4))
					{
						continue;
					}
				}
			}	


			if (ptna_set != NULL)
			{
				bool bIsAlsoDisconnectedEntry = exist_in_tco_node_addr_set(ptna_set, addrReached.interfaceAddr.ipv4);
				if (bIsAlsoDisconnectedEntry)
				{

					if (pbPossibleToFound)
					{
						*pbPossibleToFound = TRUE;
					}

					continue;
				}
			}

			if (ptna_set2 != NULL)
			{
				bool bIsAlsoDisconnectedEntry = exist_in_tco_node_addr_set(ptna_set2, addrReached.interfaceAddr.ipv4);
				if (bIsAlsoDisconnectedEntry)
				{

					if (pbPossibleToFound)
					{
						*pbPossibleToFound = TRUE;
					}

					continue;
				}
			}


			rt_entry* prteNearby = QueryRoutingTableAccordingToNodeId(node, addrReached.interfaceAddr.ipv4);


			if (dTBExchanged != NULL && prteNearby != NULL)
			{
				if (!dTBExchanged->bChildrenDetermined)
				{
					if (prteNearby->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 == reTBExchanged->rt_entry_infos.rtu_dst.interfaceAddr.ipv4)
					{

						//is a child, add to children list
						AddToChildrenList(&(dTBExchanged->children), prteNearby);

						continue;
					}
				}
			}



			if (_TEST_TIME_COMPLEXITY && puiLookupCntForRE)
			{
				uiLookupCnt++;
			}

			if (!bRequireSameRouter && prteNearby != NULL 
				|| bRequireSameRouter && prteNearby != NULL && (prteNearby->rt_router.interfaceAddr.ipv4 == reTBExchanged->rt_router.interfaceAddr.ipv4))
			{

				if (!bIncludeOldLastHop && reTBExchanged->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 != addrReached.interfaceAddr.ipv4
					|| bIncludeOldLastHop)
				{


					//must satisfy prteNearby->rt_entry_infos.rtu_metric == uiCurrentCost or prteNearby->rt_entry_infos.rtu_metric + 1 = uiCurrentCost
					if (prteNearby->rt_metric == reTBExchanged->rt_metric - 1)
					{
					

						if (g_iToAchieveSameRoute == 1)
						{

							if (bSameCost)
							{
								if (PreferredRouteForNew(prteNearby->rt_router.interfaceAddr.ipv4, prtetmp->rt_router.interfaceAddr.ipv4))
								{
									prtetmp = prteNearby;
								}
							}
							else
							{
								prtetmp = prteNearby;
							}

							bSameCost = TRUE;

							continue;

						}
						else
						{

							bSameCost = TRUE;

							prtetmp = prteNearby;

							if (prteNearby->rt_router.interfaceAddr.ipv4 == reTBExchanged->rt_router.interfaceAddr.ipv4)
							{

								//same router
								bExistSameCostWithSameRouter = TRUE;


								break;
								//break;
							}
							else
							{

								//different router

								continue;
							}

						}

						

					}

					//just do not consider any cost change


					/*
					if (!bSameCost && prteNearby->rt_metric == reTBExchanged->rt_metric 
						//comment reason: if this indirect link does exist, then it is ok, 
						//since the disconnect of direct link does not mean the disconnect of the indirect link
						//&& reTBExchanged->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 != prteNearby->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4
						)
					{


						bCostPlusOne = TRUE;

						prtetmp = prteNearby;

						continue;
					}


					if (!bSameCost && !bCostPlusOne && prteNearby->rt_metric == reTBExchanged->rt_metric + 1
						&& prteNearby->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 != reTBExchanged->rt_entry_infos.rtu_dst.interfaceAddr.ipv4)
					{

						//comment reason: if this indirect link does exist, then it is ok, 
						//since the disconnect of direct link does not mean the disconnect of the indirect link
						//rt_entry* prteNearby2 = QueryRoutingTableAccordingToNodeId(node, prteNearby->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4);

						//if (prteNearby2 != NULL)
						{
							//if (prteNearby2->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 != reTBExchanged->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4)
							{


								bCostPlusTwo = TRUE;

								prtetmp = prteNearby;


								continue;
							}
						}
					}
					*/

				}
				else
				{
					//will not happen, since it should already be deleted
				}

			}

		}


		if (dTBExchanged != NULL)
		{

			dTBExchanged->bChildrenDetermined = TRUE;
		}


		bExchangeFound =  bSameCost;// || bCostPlusOne || bCostPlusTwo;

		
		if (bExchangeFound)
		{
			if (bSameCost)
			{

				reTBExchanged->rt_entry_infos.bCostChanged = FALSE;

				reTBExchanged->rt_entry_infos.uiCostChg = 0;

				if (g_iToAchieveSameRoute == 1)
				{

					if (prtetmp->rt_router.interfaceAddr.ipv4 == reTBExchanged->rt_router.interfaceAddr.ipv4)
					{

						bExistSameCostWithSameRouter = TRUE;
					}						
				}
				

				if (bExistSameCostWithSameRouter)
				{


					reTBExchanged->rt_entry_infos.rtu_lasthop = prtetmp->rt_dst;

					if (dTBExchanged != NULL)
					{

						//dTBExchanged->bChildrenDetermined = TRUE;
						ClearChildrenList(dTBExchanged->children);

					}


				}
				else
				{

					reTBExchanged->rt_entry_infos.rtu_lasthop = prtetmp->rt_dst;


					reTBExchanged->rt_interface = prtetmp->rt_interface;
					reTBExchanged->rt_router = prtetmp->rt_router;


					if (_OLSR_MULTIPATH)
					{


						reTBExchanged->rt_entry_infos.rtu_DegreeWRTNode = prtetmp->rt_entry_infos.rtu_DegreeWRTNode;
						reTBExchanged->rt_entry_infos.rtu_DistanceWRTNode = prtetmp->rt_entry_infos.rtu_DistanceWRTNode;
						reTBExchanged->rt_entry_infos.related_neighbor = prtetmp->rt_entry_infos.related_neighbor;
					}
				}
			}
			/*
			else	//bCostPlusOne or bCostPlusTwo
			{


				reTBExchanged->rt_entry_infos.bCostChanged = TRUE;

				reTBExchanged->rt_entry_infos.rtu_lasthop = prtetmp->rt_dst;


				reTBExchanged->rt_interface = prtetmp->rt_interface;
				reTBExchanged->rt_router = prtetmp->rt_router;

				reTBExchanged->rt_metric = (UInt16) (prtetmp->rt_metric + 1);


				reTBExchanged->rt_entry_infos.rtu_DegreeWRTNode = prtetmp->rt_entry_infos.rtu_DegreeWRTNode;
				reTBExchanged->rt_entry_infos.rtu_DistanceWRTNode = prtetmp->rt_entry_infos.rtu_DistanceWRTNode;
				reTBExchanged->rt_entry_infos.related_neighbor = prtetmp->rt_entry_infos.related_neighbor;
			}
			*/


			if (bExistSameCostWithSameRouter)
			{

				reTBExchanged->rt_entry_infos.bDescendentRequireFurtherUpdate = FALSE;
			}
			else
			{

				reTBExchanged->rt_entry_infos.bDescendentRequireFurtherUpdate = TRUE;
			}


		}
		else
		{


			//need to delete


		}

	}
	else
	{
		//need to delete

	}


	if (_TEST_TIME_COMPLEXITY && puiLookupCntForRE)
	{
		*puiLookupCntForRE += uiLookupCnt;
	}


	return bExchangeFound;
}


BOOL FindRouteExchange(Node* node, rt_entry* reTBExchanged, BOOL bIncludeOldLastHop, UInt32 * puiLookupCntForRE, BOOL bRequireSameRouter)
{

	BOOL bExchangeFound = FALSE;

	UInt32 uiLookupCnt = 0;

	topology_last_entry * t_last_sym = OlsrLookupLastTopologyTableSYM(node, reTBExchanged->rt_dst);
	if (t_last_sym != NULL)
	{
		destination_list* topo_dest = NULL;
		
		topo_dest = t_last_sym->topology_list_of_destinations;

		rt_entry* prtetmp = NULL;

		BOOL bSameCost = FALSE;
		BOOL bCostPlusOne = FALSE;
		BOOL bCostPlusTwo = FALSE;
		
		BOOL bExistSameCostWithSameRouter = FALSE;

		BOOL bExist = FALSE;

		while (topo_dest != NULL)
		{
			
			Address addrReached = topo_dest->destination_node->topology_destination_dst;


			topo_dest = topo_dest->next;

			rt_entry* prteNearby = QueryRoutingTableAccordingToNodeId(node, addrReached.interfaceAddr.ipv4);


			if (_TEST_TIME_COMPLEXITY && puiLookupCntForRE)
			{
				uiLookupCnt++;
			}

			if (!bRequireSameRouter && prteNearby != NULL 
				|| bRequireSameRouter && prteNearby != NULL && (prteNearby->rt_router.interfaceAddr.ipv4 == reTBExchanged->rt_router.interfaceAddr.ipv4))
			{

				if (!bIncludeOldLastHop && reTBExchanged->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 != addrReached.interfaceAddr.ipv4
					|| bIncludeOldLastHop)
				{

					//must satisfy prteNearby->rt_entry_infos.rtu_metric == uiCurrentCost or prteNearby->rt_entry_infos.rtu_metric + 1 = uiCurrentCost
					if (prteNearby->rt_metric == reTBExchanged->rt_metric - 1)
					{

						bSameCost = TRUE;

						prtetmp = prteNearby;

						if (prteNearby->rt_router.interfaceAddr.ipv4 == reTBExchanged->rt_router.interfaceAddr.ipv4)
						{

							//same router
							bExistSameCostWithSameRouter = TRUE;
							break;
						}
						else
						{

							//different router
							
							continue;
						}

					}

					
					if (!bSameCost && prteNearby->rt_metric == reTBExchanged->rt_metric 
						//comment reason: if this indirect link does exist, then it is ok, 
						//since the disconnect of direct link does not mean the disconnect of the indirect link
						//&& reTBExchanged->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 != prteNearby->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4
						)
					{


						bCostPlusOne = TRUE;

						prtetmp = prteNearby;

						continue;
					}


					if (!bSameCost && !bCostPlusOne && prteNearby->rt_metric == reTBExchanged->rt_metric + 1
						&& prteNearby->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 != reTBExchanged->rt_entry_infos.rtu_dst.interfaceAddr.ipv4)
					{

						//comment reason: if this indirect link does exist, then it is ok, 
						//since the disconnect of direct link does not mean the disconnect of the indirect link
						//rt_entry* prteNearby2 = QueryRoutingTableAccordingToNodeId(node, prteNearby->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4);

						//if (prteNearby2 != NULL)
						{
							//if (prteNearby2->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 != reTBExchanged->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4)
							{

								
								bCostPlusTwo = TRUE;

								prtetmp = prteNearby;


								continue;
							}
						}
					}
					
				}
				else
				{
					//will not happen, since it should already be deleted
				}

			}

		}



		bExchangeFound =  bSameCost || bCostPlusOne || bCostPlusTwo;

		
		if (bExchangeFound)
		{
			if (bSameCost)
			{

				reTBExchanged->rt_entry_infos.bCostChanged = FALSE;

				reTBExchanged->rt_entry_infos.uiCostChg = 0;

			

				if (bExistSameCostWithSameRouter)
				{
					
				
					reTBExchanged->rt_entry_infos.rtu_lasthop = prtetmp->rt_dst;
					
					
				}
				else
				{
					
					reTBExchanged->rt_entry_infos.rtu_lasthop = prtetmp->rt_dst;


					reTBExchanged->rt_interface = prtetmp->rt_interface;
					reTBExchanged->rt_router = prtetmp->rt_router;
					

					if (_OLSR_MULTIPATH)
					{

						reTBExchanged->rt_entry_infos.rtu_DegreeWRTNode = prtetmp->rt_entry_infos.rtu_DegreeWRTNode;
						reTBExchanged->rt_entry_infos.rtu_DistanceWRTNode = prtetmp->rt_entry_infos.rtu_DistanceWRTNode;
						reTBExchanged->rt_entry_infos.related_neighbor = prtetmp->rt_entry_infos.related_neighbor;
					}
				}
			}
			else	//bCostPlusOne or bCostPlusTwo
			{
			

				reTBExchanged->rt_entry_infos.bCostChanged = TRUE;

				if (bCostPlusOne)
				{
					reTBExchanged->rt_entry_infos.uiCostChg = 1;
				}
				else
				{
					reTBExchanged->rt_entry_infos.uiCostChg = 2;
				}

				reTBExchanged->rt_entry_infos.rtu_lasthop = prtetmp->rt_dst;


				reTBExchanged->rt_interface = prtetmp->rt_interface;
				reTBExchanged->rt_router = prtetmp->rt_router;
				
				reTBExchanged->rt_metric = (UInt16) (prtetmp->rt_metric + 1);
				

				reTBExchanged->rt_entry_infos.rtu_DegreeWRTNode = prtetmp->rt_entry_infos.rtu_DegreeWRTNode;
				reTBExchanged->rt_entry_infos.rtu_DistanceWRTNode = prtetmp->rt_entry_infos.rtu_DistanceWRTNode;
				reTBExchanged->rt_entry_infos.related_neighbor = prtetmp->rt_entry_infos.related_neighbor;
			}


			if (bExistSameCostWithSameRouter)
			{
		
				reTBExchanged->rt_entry_infos.bDescendentRequireFurtherUpdate = FALSE;
			}
			else
			{
				
				reTBExchanged->rt_entry_infos.bDescendentRequireFurtherUpdate = TRUE;
			}


		}
		else
		{

			
			//need to delete
			
			
		}
		
	}
	else
	{
		//need to delete

	}


	if (_TEST_TIME_COMPLEXITY && puiLookupCntForRE)
	{
		*puiLookupCntForRE += uiLookupCnt;
	}


	return bExchangeFound;
}

BOOL DisconnectivetyCausedBy2HopNeighbor(Node* node, Address addrExpected2Hop, NodeAddress naExpectedNeighbor)
{
	BOOL bDisConnectivety = TRUE;

	neighbor_2_entry *two_hop_neighbor = NULL;

	two_hop_neighbor = OlsrLookup2HopNeighborTable(node, addrExpected2Hop);
	
	if (two_hop_neighbor)
	{

		neighbor_list_entry* list_1 = NULL;
		list_1 = two_hop_neighbor->neighbor_2_nblist;

		while (list_1 != NULL)
		{
			
			if (list_1->neighbor->neighbor_main_addr.interfaceAddr.ipv4 == naExpectedNeighbor)
			{
				bDisConnectivety = FALSE;
				break;
			}																

			list_1 = list_1->neighbor_next;
		}

	}
	
	return bDisConnectivety;
}


BOOL ConnectivetyCausedBy2HopNeighbor(Node* node, Address addrExpected2Hop, NodeAddress naExpectedNeighbor)
{
	
	BOOL bConnectivety = FALSE;

	neighbor_2_entry *two_hop_neighbor = NULL;

	two_hop_neighbor = OlsrLookup2HopNeighborTable(node, addrExpected2Hop);
	if (two_hop_neighbor)
	{
		neighbor_list_entry* list_1 = NULL;

		list_1 = two_hop_neighbor->neighbor_2_nblist;

		
		while (list_1 != NULL)
		{
			if (list_1->neighbor->neighbor_main_addr.interfaceAddr.ipv4 == naExpectedNeighbor)
			{
				bConnectivety = TRUE;
				break;
			}

			list_1 = list_1->neighbor_next;
		}		
	}

	
	return bConnectivety;
}


void SubFuncForLoopHelpFuncV23(Node * node, e2_s e2_current, destination_n ** list_p0, destination_n ** p_avoid_consider_list_for_p2 = NULL, UInt32 * puiLookupCnt = NULL, tco_node_addr ** ptco_avoid_consider_list = NULL)
{
		
	if (e2_current.list_p2 != NULL)
	{
		destination_n * tmp_destination = NULL;

		tmp_destination = e2_current.list_p2;

		while (tmp_destination != NULL)
		{
	
			destination_n* destination_n_1 = NULL;
			destination_list* topo_dest = NULL;
			
			if (tmp_destination->bChildrenDetermined)
			{
				destination_n * dst_child = tmp_destination->children;
				while (dst_child != NULL)
				{

					Address addrReached = dst_child->destination->rt_entry_infos.rtu_dst;							

					UInt32 uiInnerExchangeLUCnt = 0;

					OlsrCalculateRoutingTableForSinglePathTopologySearchHelpFuncV23(node, dst_child, e2_current, addrReached, tmp_destination, list_p0, p_avoid_consider_list_for_p2, &uiInnerExchangeLUCnt, ptco_avoid_consider_list);

					
					dst_child = dst_child->next;
				}
			}
			else
			{

				topology_last_entry* topo_last = OlsrLookupLastTopologyTableSYM(node, tmp_destination->destination->rt_dst);
			

				if (NULL != topo_last)
				{
					topo_dest = topo_last->topology_list_of_destinations;

					while (topo_dest != NULL)
					{

						Address addrReached = topo_dest->destination_node->topology_destination_dst;

						/*
						if (RoutingOlsrCheckMyIfaceAddress(
							node,
							topo_dest->destination_node->topology_destination_dst) != -1)
						{
							topo_dest = topo_dest->next;
							continue;
						}
						*/


						UInt32 uiInnerExchangeLUCnt = 0;


					
						OlsrCalculateRoutingTableForSinglePathTopologySearchHelpFuncV23(node, NULL, e2_current, addrReached, tmp_destination, list_p0, p_avoid_consider_list_for_p2, &uiInnerExchangeLUCnt, ptco_avoid_consider_list);


						//Peter Added for test time complexity
						/*
						if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
						{
							uiLookupCnt += uiInnerExchangeLUCnt;

							//if (node->nodeId == NODE_ID_FOR_TEST_OUTER_ANGLE || node->nodeId == NODE_ID_FOR_TEST_OUTER_EDGE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_ANGLE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_EDGE || node->nodeId == NODE_ID_FOR_TEST_CENTER)
							if (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END)
							{
								uiLookupCnt++;

							}
						}
						*/

						topo_dest = topo_dest->next;
					}
				}
			}
						

			tmp_destination = tmp_destination->next;
			//destination_n_1 = (*list_pp);
			//(*list_pp) = (*list_pp)->next;
			//MEM_free(destination_n_1);
		}

		while (e2_current.list_p2 != NULL)
		{
			destination_n* destination_n_1 = NULL;
			destination_n_1 = e2_current.list_p2;
			e2_current.list_p2 = e2_current.list_p2->next;
			MEM_free(destination_n_1);
		}

	}
}


void SubFuncForLoopHelpFuncV22(Node * node, destination_n ** list_pp, e2_s* p_e2s_n_minus_1, e2_s* p_e2s_n_0, e2_s* p_e2s_n_1, 
							   UInt32 * puiLookupCnt = NULL, tco_node_addr ** ptna_set = NULL, tco_node_addr ** ptna_set2 = NULL)
{

	if (*list_pp != NULL)
	{
					
		while (*list_pp != NULL)
		{
			
			destination_n* destination_n_1 = NULL;
			destination_list* topo_dest = NULL;
			
			
			if ((*list_pp)->bChildrenDetermined)
			{
				destination_n * dst_child = (*list_pp)->children;
				while (dst_child != NULL)
				{

					Address addrReached = dst_child->destination->rt_entry_infos.rtu_dst;							

					UInt32 uiInnerExchangeLUCnt = 0;

					OlsrCalculateRoutingTableForSinglePathTopologySearchHelpFuncV22(node, dst_child, addrReached, (*list_pp), p_e2s_n_minus_1, p_e2s_n_0, p_e2s_n_1, &uiInnerExchangeLUCnt, ptna_set, ptna_set2);

					//OlsrCalculateRoutingTableForSinglePathTopologySearchHelpFuncV24(node, dst_child, addrReached, e2_s_n.list_p1, &e2_s_n.list_p0, &list_avoid_consider_for_p1, &uiInnerExchangeLUCnt, &tco_avoid_consider_list_p1, ptco_avoid_consider_list);

					dst_child = dst_child->next;
				}
			}
			else
			{

				topology_last_entry* topo_last = OlsrLookupLastTopologyTableSYM(node, (*list_pp)->destination->rt_dst);
			
				if (NULL != topo_last)
				{
					topo_dest = topo_last->topology_list_of_destinations;

					while (topo_dest != NULL)
					{

						Address addrReached = topo_dest->destination_node->topology_destination_dst;

						/*
						if (RoutingOlsrCheckMyIfaceAddress(
							node,
							topo_dest->destination_node->topology_destination_dst) != -1)
						{
							topo_dest = topo_dest->next;
							continue;
						}
						*/


						UInt32 uiInnerExchangeLUCnt = 0;


						OlsrCalculateRoutingTableForSinglePathTopologySearchHelpFuncV22(node, NULL, addrReached, (*list_pp), p_e2s_n_minus_1, p_e2s_n_0, p_e2s_n_1, &uiInnerExchangeLUCnt, ptna_set, ptna_set2);


						//Peter Added for test time complexity
						topo_dest = topo_dest->next;
					}
				}
			}
			
			

			destination_n_1 = (*list_pp);
			(*list_pp) = (*list_pp)->next;
			MEM_free(destination_n_1);
		}

	}
}


destination_n* ProcessRoutingTableAccordingToRecentDeleteListV23(Node* node, UInt32 * pbRequireRediscovery, UInt32 * puiLookupCntForDeleteList)
{

	//destination_n * list_destination_n = NULL;

	destination_n * list_destination_delete = NULL;

	RoutingOlsr * olsr = (RoutingOlsr *) node->appData.olsr;

	tco_node_addr * tco_delete_list_tmp = olsr->recent_delete_list;	

	UInt32 uiLookupCnt = 0;

	*pbRequireRediscovery = FALSE;


	clear_tco_node_addr_set(&olsr->recent_add_list);


	UInt16 uiTCOldCost = MAX_COST;
	//if (tco_delete_list_tmp->nid == 10 && olsr->naRecentChangedAddressByTC == 15 && node->nodeId == 16)
	//{

	//DebugBreak();
	//}


	//prte and prteTC will exist or non-exist at the same time
	rt_entry* prteTC = QueryRoutingTableAccordingToNodeId(node, olsr->naRecentChangedAddressByTC);



	if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
	{
		uiLookupCnt++;
	}

	if (prteTC != NULL)
	{

		uiTCOldCost = prteTC->rt_entry_infos.rtu_metric;


		BOOL bExistReachTCFromTDNodeTBD = FALSE;

		int i_prteTCOldCost = prteTC->rt_metric;

		prteTC->rt_entry_infos.bDescendentRequireFurtherUpdate = FALSE;
		prteTC->rt_entry_infos.bCostChanged = FALSE;
		prteTC->rt_entry_infos.bRequireDelete = FALSE;
		prteTC->rt_entry_infos.uiCostChg = 0;


		while (tco_delete_list_tmp != NULL)
		{

			if (prteTC->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 == tco_delete_list_tmp->nid)
			{

				if (prteTC->rt_metric == 2)
				{

					BOOL b2HopNeighborCausedConnection = FALSE;
					b2HopNeighborCausedConnection = ConnectivetyCausedBy2HopNeighbor(node, prteTC->rt_entry_infos.rtu_dst, tco_delete_list_tmp->nid);

					if (b2HopNeighborCausedConnection)
					{

						remove_from_tco_node_addr_set(&(olsr->recent_delete_list), tco_delete_list_tmp->nid);

						break;
					}										
				}



				bExistReachTCFromTDNodeTBD = TRUE;

				remove_from_tco_node_addr_set(&(olsr->recent_delete_list), tco_delete_list_tmp->nid);


				break;
			}

			tco_delete_list_tmp = tco_delete_list_tmp->next;
		}


		e2_s e2_plus_zero;
		e2_s e2_plus_one;
		e2_s e2_plus_two;
		e2_s e2_plus_three;


		e2_plus_zero.list_delete = NULL;
		e2_plus_zero.list_p0 = NULL;
		e2_plus_zero.list_p1 = NULL;
		e2_plus_zero.list_p2 = NULL;


		e2_plus_one.list_delete = NULL;
		e2_plus_one.list_p0 = NULL;
		e2_plus_one.list_p1 = NULL;
		e2_plus_one.list_p2 = NULL;


		e2_plus_two.list_delete = NULL;
		e2_plus_two.list_p0 = NULL;
		e2_plus_two.list_p1 = NULL;
		e2_plus_two.list_p2 = NULL;



		e2_plus_three.list_delete = NULL;
		e2_plus_three.list_p0 = NULL;
		e2_plus_three.list_p1 = NULL;
		e2_plus_three.list_p2 = NULL;




		BOOL bExistReachTCFromTDNodeTBDWithoutFindPlus2Exchange = FALSE;

		BOOL bPlusTwoExchangeForTSFound = FALSE;
		rt_entry* tmp_2ExchgForTS = NULL;

		tco_node_addr * ATS_list = NULL;


		tco_node_addr * disconnected_list = NULL;


		destination_n list_destination_tc_tmp;


		memset(
			&list_destination_tc_tmp,
			0,
			sizeof(destination_n));


		/*
		list_destination_tc_tmp = (destination_n* )
			MEM_malloc(sizeof(destination_n));

		memset(
			list_destination_tc_tmp,
			0,
			*/
		
		destination_n * p_list_destination_ats = NULL;

		if (bExistReachTCFromTDNodeTBD)
		{
			//DebugBreak();
			//the same as bExistReachTCFromTDNodeTBD for this specific case

			//find exchange for this,
			//if can not find, then do not do following further exchange
			BOOL bExchangeFound = FindRouteExchangeV22(node, &list_destination_tc_tmp, prteTC, FALSE, NULL, &uiLookupCnt);

			if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
			{

				*puiLookupCntForDeleteList = uiLookupCnt;
			}

			if (!bExchangeFound)
			{

				//OlsrDeleteRoutingTable(prteTC);
				//prteTC = NULL;

				if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
				{
					//uiLookupCnt++;
					*puiLookupCntForDeleteList = uiLookupCnt;
				}


				//to try to consider the ATS and DATS 0 exchange condition, which may also cause +2 exchange for TS



				bExistReachTCFromTDNodeTBDWithoutFindPlus2Exchange = TRUE;
				//*pbRequireRediscovery = TRUE;
				//return NULL;
			}
			else
			{
				
				destination_n* list_destination_tmp;
				list_destination_tmp = (destination_n* )
					MEM_malloc(sizeof(destination_n));

				memset(
					list_destination_tmp,
					0,
					sizeof(destination_n));

				list_destination_tmp->destination = prteTC;


				if (prteTC->rt_entry_infos.bDescendentRequireFurtherUpdate)
				{
					if (prteTC->rt_entry_infos.uiCostChg == 0)
					{
						//only route change
						list_destination_tmp->next = e2_plus_zero.list_p0; 
						e2_plus_zero.list_p0 = list_destination_tmp;

					}
					else
					{

						if (prteTC->rt_entry_infos.uiCostChg == 1)
						{
							
							list_destination_tmp->next = e2_plus_one.list_p1;
							e2_plus_one.list_p1 = list_destination_tmp;

						}
						else	//uiCostChg == 2
						{
							list_destination_tmp->next = e2_plus_two.list_p2;
							e2_plus_two.list_p2 = list_destination_tmp;

						}
					}

				}				

			}


			if (prteTC->rt_entry_infos.bDescendentRequireFurtherUpdate || bExistReachTCFromTDNodeTBDWithoutFindPlus2Exchange)
			{

				// need to find whether ATS can be exchanged by +0
				if (list_destination_tc_tmp.bChildrenDetermined)
				{
					destination_n * dst_child = list_destination_tc_tmp.children;
					while (dst_child != NULL)
					{

						Address addrReached = dst_child->destination->rt_entry_infos.rtu_dst;							

						UInt32 uiInnerExchangeLUCnt = 0;

						rt_entry* prteNearby = dst_child->destination;
						if (prteNearby != NULL)
						{

							if (prteNearby->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 == olsr->naRecentChangedAddressByTC)
							{

								prteNearby->rt_entry_infos.uiCostChg = 0;

								prteNearby->rt_entry_infos.bCostChanged = FALSE;
								prteNearby->rt_entry_infos.bDescendentRequireFurtherUpdate = FALSE;
								prteNearby->rt_entry_infos.bRequireDelete = FALSE;

								BOOL bExchangeFound = FindRouteExchangeV20(node, dst_child, prteNearby, !bExistReachTCFromTDNodeTBDWithoutFindPlus2Exchange, &uiLookupCnt);
								if (bExchangeFound)
								{


									if (bExistReachTCFromTDNodeTBDWithoutFindPlus2Exchange)
									{

										bPlusTwoExchangeForTSFound = TRUE;

										if (tmp_2ExchgForTS == NULL)
										{

											tmp_2ExchgForTS = prteNearby;
										}
										else
										{

											if (g_iToAchieveSameRoute == 1)
											{	

												if (PreferredRouteForNew(prteNearby->rt_entry_infos.rtu_router.interfaceAddr.ipv4, tmp_2ExchgForTS->rt_entry_infos.rtu_router.interfaceAddr.ipv4))
												{
													tmp_2ExchgForTS = prteNearby;
												}
											}
											
										}
									}
									else
									{

										if (g_iToAchieveSameRoute == 1)
										{
											if (bExistReachTCFromTDNodeTBD && prteTC->rt_entry_infos.bDescendentRequireFurtherUpdate && prteTC->rt_entry_infos.uiCostChg == 2)
											{

												if (PreferredRouteForNew(prteNearby->rt_entry_infos.rtu_router.interfaceAddr.ipv4, prteTC->rt_entry_infos.rtu_router.interfaceAddr.ipv4))
												{
													//change route for its old parent to become the new parent

													prteTC->rt_interface = prteNearby->rt_interface;

									
										
													/*
													if (_OLSR_MULTIPATH)
													{

													
														prteTC->rt_entry_infos.rtu_DegreeWRTNode = prteNearby->rt_entry_infos.rtu_DegreeWRTNode;
														prteTC->rt_entry_infos.rtu_DistanceWRTNode = prteNearby->rt_entry_infos.rtu_DistanceWRTNode;
														prteTC->rt_entry_infos.related_neighbor = prteNearby->rt_entry_infos.related_neighbor;
													}
													*/
																		
										
													prteTC->rt_entry_infos.rtu_lasthop = prteNearby->rt_entry_infos.rtu_dst;									
													
													prteTC->rt_router = prteNearby->rt_router;									
													
												}	
											}
										}
									}


									if (prteNearby->rt_entry_infos.bDescendentRequireFurtherUpdate)
									{

										//add to list

										destination_n* list_destination_tmp;
										list_destination_tmp = (destination_n* )
											MEM_malloc(sizeof(destination_n));

										memset(
											list_destination_tmp,
											0,
											sizeof(destination_n));

										list_destination_tmp->destination = prteNearby;

										{
											list_destination_tmp->children = dst_child->children;
											list_destination_tmp->bChildrenDetermined = dst_child->bChildrenDetermined;

											dst_child->children = NULL;
										}


										//only route change
										list_destination_tmp->next = e2_plus_one.list_p0;
										e2_plus_one.list_p0 = list_destination_tmp;


									}
									else
									{
										//do not need to add to list, since all their descendants are not require change
									}
								}
								else
								{
									insert_into_tco_node_addr_set(&(ATS_list), addrReached.interfaceAddr.ipv4);


									destination_n* list_destination_tmp;
									list_destination_tmp = (destination_n* )
										MEM_malloc(sizeof(destination_n));

									memset(
										list_destination_tmp,
										0,
										sizeof(destination_n));

									list_destination_tmp->destination = prteNearby;

									{
										list_destination_tmp->children = dst_child->children;
										list_destination_tmp->bChildrenDetermined = dst_child->bChildrenDetermined;

										dst_child->children = NULL;
									}



									//only route change
									list_destination_tmp->next = p_list_destination_ats;
									p_list_destination_ats = list_destination_tmp;
								
									
								}
							}
						}

						//OlsrCalculateRoutingTableForSinglePathTopologySearchHelpFuncV24(node, dst_child, addrReached, e2_plus_two.list_p1, &e2_plus_two.list_p0, 
						//	&list_avoid_consider_for_p1, &uiInnerExchangeLUCnt, &tco_avoid_consider_list_p1, &olsr->recent_delete_list);

						//dst_child = dst_child->next;

						destination_n * destination_n_1 = dst_child;						
						dst_child = dst_child->next;

						MEM_free(destination_n_1);
					}
				}
							
			}
			
		}
		else
		{


		}



		BOOL bEncounterCannotFindExchange = FALSE;

		destination_n * p_list_destination_dts = NULL;

		tco_delete_list_tmp = olsr->recent_delete_list;
		//now it should not including the entry get to TCNode, since it is removed from the list,
		//so only those nodes reached (it is possible that nodes can be reached but consider TCNode as last hop)
		//by TCNode is remained 



		//int iDisconnectCount = 0;

		while (tco_delete_list_tmp != NULL)
		{

			rt_entry* prte = QueryRoutingTableAccordingToNodeId(node, tco_delete_list_tmp->nid);

			if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
			{
				uiLookupCnt++;
			}

			if (prte != NULL)
			{

				if (prte->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 == olsr->naRecentChangedAddressByTC)
				{

					if (prte->rt_metric == 2)
					{
						BOOL b2HopNeighborCausedConnection = FALSE;

						b2HopNeighborCausedConnection = ConnectivetyCausedBy2HopNeighbor(node, prte->rt_entry_infos.rtu_dst, olsr->naRecentChangedAddressByTC);
						if (b2HopNeighborCausedConnection)
						{

							//remove_from_tco_node_addr_set(&(olsr->recent_delete_list), tco_delete_list_tmp->nid);

							tco_delete_list_tmp = tco_delete_list_tmp->next;

							continue;
						}
					}

					insert_into_tco_node_addr_set(&(disconnected_list), tco_delete_list_tmp->nid);
					//iDisconnectCount++;
					

					destination_n* list_destination_tmp;
					list_destination_tmp = (destination_n* )
						MEM_malloc(sizeof(destination_n));

					memset(
						list_destination_tmp,
						0,
						sizeof(destination_n));

					list_destination_tmp->destination = prte;


					//only route change
					list_destination_tmp->next = p_list_destination_dts;
					p_list_destination_dts = list_destination_tmp;



				}
				else
				{
					//it is possible that nodes can be reached but not consider TCNode as last hop
					//skip these nodes

				}

			}
			else
			{

				//should not happen
			}


			tco_delete_list_tmp = tco_delete_list_tmp->next;
		}


		destination_n * p_list_destination_dts2 = NULL;
		
		{

			// need to find whether DATS can be exchanged by +0
			
			tco_node_addr * tmp_disconnected_list = NULL;

			if (disconnected_list != NULL)
			{
				
				//while (disconnected_list != NULL)
				{
					
					//copy the set

					/*
					tco_node_addr * tmp_addr = disconnected_list;
					while (tmp_addr != NULL)
					{

						insert_into_tco_node_addr_set(&(tmp_disconnected_list), tmp_addr->nid);
						tmp_addr = tmp_addr->next;
					}

					tco_node_addr * tmp_addr_tmp = tmp_disconnected_list;

					*/
					//BOOL bAtleastFindOne = FALSE;
					destination_n * p_destination_tmp = p_list_destination_dts;
					while (p_destination_tmp != NULL)
					{

						rt_entry* prte = p_destination_tmp->destination;

						if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
						{
							uiLookupCnt++;
						}

						if (prte != NULL)
						{

							//the exchange here need to support unconsider set,
							//to avoid circular dependency 

							prte->rt_entry_infos.uiCostChg = 0;

							prte->rt_entry_infos.bCostChanged = FALSE;
							prte->rt_entry_infos.bDescendentRequireFurtherUpdate = FALSE;
							prte->rt_entry_infos.bRequireDelete = FALSE;


							BOOL bExchangeFound = FindRouteExchangeV20(node, p_destination_tmp, prte, FALSE, &uiLookupCnt);
							if (!bExchangeFound)
							{

								destination_n* list_destination_tmp;
								list_destination_tmp = (destination_n* )
									MEM_malloc(sizeof(destination_n));

								memset(
									list_destination_tmp,
									0,
									sizeof(destination_n));

								list_destination_tmp->destination = prte;


								{
									list_destination_tmp->children = p_destination_tmp->children;
									list_destination_tmp->bChildrenDetermined = p_destination_tmp->bChildrenDetermined;

									p_destination_tmp->children = NULL;
								}

								
								list_destination_tmp->next = p_list_destination_dts2;
								p_list_destination_dts2 = list_destination_tmp;

							}
							else
							{

								//For deleted entry, the link is disappear, so can not act as exchange
								/*
								if (bExistReachTCFromTDNodeTBDWithoutFindPlus2Exchange)
								{

									bPlusTwoExchangeForTSFound = TRUE;

									if (tmp_2ExchgForTS == NULL)
									{

										tmp_2ExchgForTS = prte;
									}
								
								}
								*/
								

								remove_from_tco_node_addr_set(&(disconnected_list), prte->rt_entry_infos.rtu_dst.interfaceAddr.ipv4);
								//insert_into_tco_node_addr_set(&(found_list), tmp_addr_tmp->nid);

								//bAtleastFindOne = TRUE;

								if (prte->rt_entry_infos.bDescendentRequireFurtherUpdate)
								{

									destination_n* list_destination_tmp;
									list_destination_tmp = (destination_n* )
										MEM_malloc(sizeof(destination_n));

									memset(
										list_destination_tmp,
										0,
										sizeof(destination_n));

									list_destination_tmp->destination = prte;


									{
										list_destination_tmp->children = p_destination_tmp->children;
										list_destination_tmp->bChildrenDetermined = p_destination_tmp->bChildrenDetermined;

										p_destination_tmp->children = NULL;
									}

									//only route change

									list_destination_tmp->next = e2_plus_one.list_p0;
									e2_plus_one.list_p0 = list_destination_tmp;
									

									
								}
								else
								{
									//perfect exchange
								}

							}
						}

						//p_destination_tmp = p_destination_tmp->next;

						destination_n * destination_n_1 = p_destination_tmp;						
						p_destination_tmp = p_destination_tmp->next;

						MEM_free(destination_n_1);
					}

					/*
					if (tmp_disconnected_list != NULL)
					{
						clear_tco_node_addr_set(&tmp_disconnected_list);
					}
					*/

				}				
			}
			else
			{
				//
			}

		}


		

		//BOOL bPlusTwoExchangeForTSFound = FALSE;
	
		if (bExistReachTCFromTDNodeTBDWithoutFindPlus2Exchange)
		{

			if (bPlusTwoExchangeForTSFound)
			{

				prteTC->rt_entry_infos.bDescendentRequireFurtherUpdate = TRUE;
				prteTC->rt_entry_infos.bCostChanged = TRUE;
				//prteTC->rt_entry_infos.bRequireDelete = FALSE;
				prteTC->rt_entry_infos.uiCostChg = 2;


				//prteTC->rt_entry_infos.bCostChanged = TRUE;

				prteTC->rt_entry_infos.rtu_lasthop = tmp_2ExchgForTS->rt_dst;


				prteTC->rt_interface = tmp_2ExchgForTS->rt_interface;
				prteTC->rt_router = tmp_2ExchgForTS->rt_router;

				prteTC->rt_metric = (UInt16) (tmp_2ExchgForTS->rt_metric + 1);


				if (_OLSR_MULTIPATH)
				{

					prteTC->rt_entry_infos.rtu_DegreeWRTNode = tmp_2ExchgForTS->rt_entry_infos.rtu_DegreeWRTNode;
					prteTC->rt_entry_infos.rtu_DistanceWRTNode = tmp_2ExchgForTS->rt_entry_infos.rtu_DistanceWRTNode;
					prteTC->rt_entry_infos.related_neighbor = tmp_2ExchgForTS->rt_entry_infos.related_neighbor;

				}


				
				destination_n* list_destination_tmp;
				list_destination_tmp = (destination_n* )
					MEM_malloc(sizeof(destination_n));

				memset(
					list_destination_tmp,
					0,
					sizeof(destination_n));

				list_destination_tmp->destination = prteTC;

					
				list_destination_tmp->next = e2_plus_two.list_p2;
				e2_plus_two.list_p2 = list_destination_tmp;
				
			}
			else
			{

				//deal with delete
				
				prteTC->rt_metric = MAX_COST;

				
				destination_n* list_destination_tmp;
				list_destination_tmp = (destination_n* )
					MEM_malloc(sizeof(destination_n));

				memset(
					list_destination_tmp,
					0,
					sizeof(destination_n));

				list_destination_tmp->destination = prteTC;

		
				list_destination_tmp->next = e2_plus_zero.list_delete;
				e2_plus_zero.list_delete = list_destination_tmp;				

			}			
					
		}


		if (g_iSpecailDebug == 1)
		{

			printf("\n-------------------------------- Special Debug After +0 exchange finished ----------------------------");


			SpecialDebug(node, DEBUG_NODE_ID, DEBUG_ENTRY_ID);


		}


		//backup for 22 exchange  for +2
		tco_node_addr * disconnected_list_backup = NULL;
		tco_node_addr * tmp_addr2 = disconnected_list;
		while (tmp_addr2 != NULL)
		{

			insert_into_tco_node_addr_set(&(disconnected_list_backup), tmp_addr2->nid);
			tmp_addr2 = tmp_addr2->next;
		}



		tco_node_addr * ATS_list_backup = NULL;
		tmp_addr2 = ATS_list;
		while (tmp_addr2 != NULL)
		{

			insert_into_tco_node_addr_set(&(ATS_list_backup), tmp_addr2->nid);
			tmp_addr2 = tmp_addr2->next;
		}



		destination_n * p_list_destination_dts3 = NULL;

		{

			// need to find whether DATS can be exchanged by +1, since all +0 (list_destination_TS_plus_one) are determined

			//tco_node_addr * tmp_disconnected_list = NULL;

			if (disconnected_list != NULL)
			{

				//while (disconnected_list != NULL)
				{

					//copy the set

					/*
					tco_node_addr * tmp_addr = disconnected_list;
					while (tmp_addr != NULL)
					{

						insert_into_tco_node_addr_set(&(tmp_disconnected_list), tmp_addr->nid);
						tmp_addr = tmp_addr->next;
					}

					tco_node_addr * tmp_addr_tmp = tmp_disconnected_list;
					*/

					//BOOL bAtleastFindOne = FALSE;

					destination_n * p_destination_tmp = p_list_destination_dts2;

					while (p_destination_tmp != NULL)
					{

						rt_entry* prte = p_destination_tmp->destination;

						if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
						{
							uiLookupCnt++;
						}

						if (prte != NULL)
						{

							//the exchange here need to support unconsider set,
							//to avoid circular dependency 

							prte->rt_entry_infos.uiCostChg = 0;

							prte->rt_entry_infos.bCostChanged = FALSE;
							prte->rt_entry_infos.bDescendentRequireFurtherUpdate = FALSE;
							prte->rt_entry_infos.bRequireDelete = FALSE;


							BOOL bExchangeFound = FindRouteExchangeV21(node,  p_destination_tmp, prte, FALSE, NULL, &uiLookupCnt, FALSE, &ATS_list, &disconnected_list, NULL, 
																		&disconnected_list_backup, &ATS_list_backup);
							if (!bExchangeFound)
							{

								destination_n* list_destination_tmp;
								list_destination_tmp = (destination_n* )
									MEM_malloc(sizeof(destination_n));

								memset(
									list_destination_tmp,
									0,
									sizeof(destination_n));

								list_destination_tmp->destination = prte;


								{
									list_destination_tmp->children = p_destination_tmp->children;
									list_destination_tmp->bChildrenDetermined = p_destination_tmp->bChildrenDetermined;

									p_destination_tmp->children = NULL;
								}


								list_destination_tmp->next = p_list_destination_dts3;
								p_list_destination_dts3 = list_destination_tmp;

							}
							else
							{

								remove_from_tco_node_addr_set(&(disconnected_list), prte->rt_entry_infos.rtu_dst.interfaceAddr.ipv4);
								//insert_into_tco_node_addr_set(&(found_list), tmp_addr_tmp->nid);

								//bAtleastFindOne = TRUE;

								if (prte->rt_entry_infos.bDescendentRequireFurtherUpdate)
								{

									if (prte->rt_entry_infos.uiCostChg == 1)
									{
										destination_n* list_destination_tmp;
										list_destination_tmp = (destination_n* )
											MEM_malloc(sizeof(destination_n));

										memset(
											list_destination_tmp,
											0,
											sizeof(destination_n));

										list_destination_tmp->destination = prte;

										{
											list_destination_tmp->children = p_destination_tmp->children;
											list_destination_tmp->bChildrenDetermined = p_destination_tmp->bChildrenDetermined;

											p_destination_tmp->children = NULL;
										}


										list_destination_tmp->next = e2_plus_two.list_p1;
										e2_plus_two.list_p1 = list_destination_tmp;

									}
									else
									{
										//should not happen
									}

								}
								else
								{
									//perfect exchange
									//should not happen
								}

							}
						}

						destination_n * destination_n_1 = p_destination_tmp;						
						p_destination_tmp = p_destination_tmp->next;

						MEM_free(destination_n_1);
					}


					/*
					if (tmp_disconnected_list != NULL)
					{
						clear_tco_node_addr_set(&tmp_disconnected_list);
					}
					*/

				}


			}
			else
			{
				//
			}


		}


		
		
		destination_n * p_list_destination_ats2 = NULL;
		if (!bExistReachTCFromTDNodeTBD)
		{

			//no ATS, DATS have tried the +0 and +1 case

			
		}
		else //(bExistReachTCFromTDNodeTBD && prteTC->rt_entry_infos.bDescendentRequireFurtherUpdate)
		{

			//topology_last_entry * t_last_sym = OlsrLookupLastTopologyTableSYM(node, prteTC->rt_dst);

			if (prteTC->rt_entry_infos.bDescendentRequireFurtherUpdate)
			{

				if (prteTC->rt_entry_infos.uiCostChg != 0)
				{

					if (prteTC->rt_entry_infos.uiCostChg == 2)
					{
						//plus two
						//destination_list* topo_dest = NULL;
						//topo_dest = t_last_sym->topology_list_of_destinations;


						/*
						tco_node_addr * tmp_ATS_list = NULL;
						tco_node_addr * tmp_ATS = ATS_list;

						//copy the set

						//tco_node_addr * tmp_addr = disconnected_list;
						while (tmp_ATS != NULL)
						{

							insert_into_tco_node_addr_set(&(tmp_ATS_list), tmp_ATS->nid);
							tmp_ATS = tmp_ATS->next;
						}

						tmp_ATS = tmp_ATS_list;
						*/

						destination_n * p_destination_tmp = p_list_destination_ats;
						while (p_destination_tmp != NULL)
						{
							//Address addrReached = topo_dest->destination_node->topology_destination_dst;

							//NodeAddress naReachedId = tmp_ATS->nid;

							//tmp_ATS = tmp_ATS->next;

							rt_entry* prteNearby = p_destination_tmp->destination;

							if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
							{
								uiLookupCnt++;
							}

							if (prteNearby != NULL)
							{

								if (prteNearby->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 == olsr->naRecentChangedAddressByTC)
								{
									prteNearby->rt_entry_infos.uiCostChg = 0;

									prteNearby->rt_entry_infos.bCostChanged = FALSE;
									prteNearby->rt_entry_infos.bDescendentRequireFurtherUpdate = FALSE;
									prteNearby->rt_entry_infos.bRequireDelete = FALSE;

									BOOL bExchangeFound = FindRouteExchangeV21(node, p_destination_tmp, prteNearby, FALSE, NULL, &uiLookupCnt, FALSE, &ATS_list, &disconnected_list);
									if (bExchangeFound)
									{

										if (prteNearby->rt_entry_infos.bDescendentRequireFurtherUpdate)
										{

											//add to list

											destination_n* list_destination_tmp;
											list_destination_tmp = (destination_n* )
												MEM_malloc(sizeof(destination_n));

											memset(
												list_destination_tmp,
												0,
												sizeof(destination_n));

											list_destination_tmp->destination = prteNearby;

											{
												list_destination_tmp->children = p_destination_tmp->children;
												list_destination_tmp->bChildrenDetermined = p_destination_tmp->bChildrenDetermined;

												p_destination_tmp->children = NULL;
											}

															
											list_destination_tmp->next = e2_plus_two.list_p1;
											e2_plus_two.list_p1 = list_destination_tmp;
											

										}
										else
										{
											//do not need to add to list, since all their descendants are not require change
											//should never happen

										}

										remove_from_tco_node_addr_set(&ATS_list, prteNearby->rt_entry_infos.rtu_dst.interfaceAddr.ipv4);
									}
									else
									{


										//***g_iToAchieveSameRoute
										//insert_into_tco_node_addr_set(&(ATS_list), addrReached.interfaceAddr.ipv4);


										if (g_iToAchieveSameRoute == 1)
										{
											//should find, since at least prteTC works.
											//for same route, since maybe some of the FindRouteExchangeV21 for AST list are not yet finished, 
											//so postpond this step later
											//bExchangeFound = FindRouteExchangeV22(node, prteNearby, TRUE, prteTC, &uiLookupCnt, FALSE, &ATS_list, &disconnected_list, &ATS_list_backup, &disconnected_list_backup);
											

											destination_n* list_destination_tmp;
											list_destination_tmp = (destination_n* )
												MEM_malloc(sizeof(destination_n));

											memset(
												list_destination_tmp,
												0,
												sizeof(destination_n));

											list_destination_tmp->destination = prteNearby;

											{
												list_destination_tmp->children = p_destination_tmp->children;
												list_destination_tmp->bChildrenDetermined = p_destination_tmp->bChildrenDetermined;

												p_destination_tmp->children = NULL;
											}


											list_destination_tmp->next = p_list_destination_ats2;
											p_list_destination_ats2 = list_destination_tmp;
										
										}
										else
										{
											prteNearby->rt_entry_infos.uiCostChg = 2;

											prteNearby->rt_entry_infos.bCostChanged = TRUE;
											prteNearby->rt_entry_infos.bDescendentRequireFurtherUpdate = TRUE;
											prteNearby->rt_entry_infos.bRequireDelete = FALSE;


											prteNearby->rt_entry_infos.rtu_lasthop = prteTC->rt_dst;


											prteNearby->rt_interface = prteTC->rt_interface;
											prteNearby->rt_router = prteTC->rt_router;

											prteNearby->rt_metric = (UInt16) (prteTC->rt_metric + 1);


											if (_OLSR_MULTIPATH)
											{

												prteNearby->rt_entry_infos.rtu_DegreeWRTNode = prteTC->rt_entry_infos.rtu_DegreeWRTNode;
												prteNearby->rt_entry_infos.rtu_DistanceWRTNode = prteTC->rt_entry_infos.rtu_DistanceWRTNode;
												prteNearby->rt_entry_infos.related_neighbor = prteTC->rt_entry_infos.related_neighbor;
											}


											if (prteNearby->rt_entry_infos.uiCostChg == 2)
											{


												//add to list

												destination_n* list_destination_tmp;
												list_destination_tmp = (destination_n* )
													MEM_malloc(sizeof(destination_n));

												memset(
													list_destination_tmp,
													0,
													sizeof(destination_n));

												list_destination_tmp->destination = prteNearby;

												{
													list_destination_tmp->children = p_destination_tmp->children;
													list_destination_tmp->bChildrenDetermined = p_destination_tmp->bChildrenDetermined;

													p_destination_tmp->children = NULL;
												}


												list_destination_tmp->next = e2_plus_three.list_p2;
												e2_plus_three.list_p2 = list_destination_tmp;

											}

											remove_from_tco_node_addr_set(&ATS_list, prteNearby->rt_entry_infos.rtu_dst.interfaceAddr.ipv4);
										}
									}							
									
								}
							}

							destination_n * destination_n_1 = p_destination_tmp;						
							p_destination_tmp = p_destination_tmp->next;

							MEM_free(destination_n_1);

						}


						/*
						if (tmp_ATS_list != NULL)
						{
							clear_tco_node_addr_set(&tmp_ATS_list);
						}
						*/


					}
					else
					{
						//plus one
						//destination_list* topo_dest = NULL;
						//topo_dest = t_last_sym->topology_list_of_destinations;

						/*
						tco_node_addr * tmp_ATS_list = NULL;
						tco_node_addr * tmp_ATS = ATS_list;

						//copy the set

						//tco_node_addr * tmp_addr = disconnected_list;
						while (tmp_ATS != NULL)
						{

							insert_into_tco_node_addr_set(&(tmp_ATS_list), tmp_ATS->nid);
							tmp_ATS = tmp_ATS->next;
						}

						tmp_ATS = tmp_ATS_list;
						*/

						destination_n * p_destination_tmp = p_list_destination_ats;
						while (p_destination_tmp != NULL)
						{

							//Address addrReached = topo_dest->destination_node->topology_destination_dst;
							//NodeAddress naReachedId = tmp_ATS->nid;

							//tmp_ATS = tmp_ATS->next;

							rt_entry* prteNearby = p_destination_tmp->destination;

							if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
							{
								uiLookupCnt++;
							}

							if (prteNearby != NULL)
							{

								if (prteNearby->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 == olsr->naRecentChangedAddressByTC)
								{


									//***g_iToAchieveSameRoute

									if (g_iToAchieveSameRoute == 1)
									{
										prteNearby->rt_entry_infos.uiCostChg = 0;

										prteNearby->rt_entry_infos.bCostChanged = FALSE;
										prteNearby->rt_entry_infos.bDescendentRequireFurtherUpdate = FALSE;
										prteNearby->rt_entry_infos.bRequireDelete = FALSE;

										FindRouteExchangeV21(node, p_destination_tmp, prteNearby, TRUE, prteTC, &uiLookupCnt, FALSE, &ATS_list, &disconnected_list);

									}
									else
									{

										//can be simplified without call FindRouteExchangeV21 since +0 case has already been processed.
										prteNearby->rt_entry_infos.uiCostChg = 1;

										prteNearby->rt_entry_infos.bCostChanged = TRUE;
										prteNearby->rt_entry_infos.bDescendentRequireFurtherUpdate = TRUE;
										prteNearby->rt_entry_infos.bRequireDelete = FALSE;

										prteNearby->rt_entry_infos.rtu_lasthop = prteTC->rt_dst;


										prteNearby->rt_interface = prteTC->rt_interface;
										prteNearby->rt_router = prteTC->rt_router;

										prteNearby->rt_metric = (UInt16) (prteTC->rt_metric + 1);


										if (_OLSR_MULTIPATH)
										{


											prteNearby->rt_entry_infos.rtu_DegreeWRTNode = prteTC->rt_entry_infos.rtu_DegreeWRTNode;
											prteNearby->rt_entry_infos.rtu_DistanceWRTNode = prteTC->rt_entry_infos.rtu_DistanceWRTNode;
											prteNearby->rt_entry_infos.related_neighbor = prteTC->rt_entry_infos.related_neighbor;
										}

									}

									


									//BOOL bExchangeFound = FindRouteExchangeV21(node, prteNearby, TRUE, prteTC, &uiLookupCnt);
									//if (bExchangeFound)
									{

										if (prteNearby->rt_entry_infos.bDescendentRequireFurtherUpdate)
										{
																					
											if (prteNearby->rt_entry_infos.uiCostChg == 1)
											{

												//add to list

												destination_n* list_destination_tmp;
												list_destination_tmp = (destination_n* )
													MEM_malloc(sizeof(destination_n));

												memset(
													list_destination_tmp,
													0,
													sizeof(destination_n));

												list_destination_tmp->destination = prteNearby;

												{
													list_destination_tmp->children = p_destination_tmp->children;
													list_destination_tmp->bChildrenDetermined = p_destination_tmp->bChildrenDetermined;

													p_destination_tmp->children = NULL;
												}


												//cost change, more specificly, plus one
												list_destination_tmp->next = e2_plus_two.list_p1;
												e2_plus_two.list_p1 = list_destination_tmp;

											}
											/*
											else
											{
												//only route change: should never happen
												list_destination_tmp->next = list_destination_TS_plus_one;
												list_destination_TS_plus_one = list_destination_tmp;
											}
											*/
									


											remove_from_tco_node_addr_set(&ATS_list, prteNearby->rt_entry_infos.rtu_dst.interfaceAddr.ipv4);
										}
										/*
										else
										{
											//do not need to add to list, since all their descendants are not require change
										}
										*/

									}
									/*
									else
									{

										//will never happen, since at least the TC is ok,
									}
									*/

								}
							}

							destination_n * destination_n_1 = p_destination_tmp;						
							p_destination_tmp = p_destination_tmp->next;

							MEM_free(destination_n_1);
						}


						/*
						if (tmp_ATS_list != NULL)
						{
							clear_tco_node_addr_set(&tmp_ATS_list);
						}
						*/

					}


				}
				else
				{
					//only route change
					//should have been done
				

				}

			}
			else
			{
				if (bExistReachTCFromTDNodeTBDWithoutFindPlus2Exchange && !bPlusTwoExchangeForTSFound)
				{

					/*
					tco_node_addr * tmp_ATS_list = NULL;
					tco_node_addr * tmp_ATS = ATS_list;

					//copy the set

					//tco_node_addr * tmp_addr = disconnected_list;
					while (tmp_ATS != NULL)
					{

						insert_into_tco_node_addr_set(&(tmp_ATS_list), tmp_ATS->nid);
						tmp_ATS = tmp_ATS->next;
					}

					tmp_ATS = tmp_ATS_list;
					*/

					destination_n * p_destination_tmp = p_list_destination_ats;
					while (p_destination_tmp != NULL)
					{
						//Address addrReached = topo_dest->destination_node->topology_destination_dst;

						//NodeAddress naReachedId = tmp_ATS->nid;

						//tmp_ATS = tmp_ATS->next;

						rt_entry* prteNearby = p_destination_tmp->destination;

						if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
						{
							uiLookupCnt++;
						}

						if (prteNearby != NULL)
						{

							if (prteNearby->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 == olsr->naRecentChangedAddressByTC)
							{
								prteNearby->rt_entry_infos.uiCostChg = 0;

								prteNearby->rt_entry_infos.bCostChanged = FALSE;
								prteNearby->rt_entry_infos.bDescendentRequireFurtherUpdate = FALSE;
								prteNearby->rt_entry_infos.bRequireDelete = FALSE;

								BOOL bExchangeFound = FindRouteExchangeV21(node, p_destination_tmp, prteNearby, FALSE, NULL, &uiLookupCnt, FALSE, &ATS_list, &disconnected_list);
								if (bExchangeFound)
								{

									remove_from_tco_node_addr_set(&ATS_list, prteNearby->rt_entry_infos.rtu_dst.interfaceAddr.ipv4);

									if (prteNearby->rt_entry_infos.bDescendentRequireFurtherUpdate)
									{

										//add to list

										destination_n* list_destination_tmp;
										list_destination_tmp = (destination_n* )
											MEM_malloc(sizeof(destination_n));

										memset(
											list_destination_tmp,
											0,
											sizeof(destination_n));

										list_destination_tmp->destination = prteNearby;

										{
											list_destination_tmp->children = p_destination_tmp->children;
											list_destination_tmp->bChildrenDetermined = p_destination_tmp->bChildrenDetermined;

											p_destination_tmp->children = NULL;
										}


										list_destination_tmp->next = e2_plus_two.list_p1;
										e2_plus_two.list_p1 = list_destination_tmp;


									}
									else
									{
										//do not need to add to list, since all their descendants are not require change
										//should never happen

									}
								}
								else
								{
									//insert_into_tco_node_addr_set(&(ATS_list), addrReached.interfaceAddr.ipv4);

									destination_n* list_destination_tmp;
									list_destination_tmp = (destination_n* )
										MEM_malloc(sizeof(destination_n));

									memset(
										list_destination_tmp,
										0,
										sizeof(destination_n));

									list_destination_tmp->destination = prteNearby;

									{
										list_destination_tmp->children = p_destination_tmp->children;
										list_destination_tmp->bChildrenDetermined = p_destination_tmp->bChildrenDetermined;

										p_destination_tmp->children = NULL;
									}


									list_destination_tmp->next = p_list_destination_ats2;
									p_list_destination_ats2 = list_destination_tmp;

								}

							}
						}


						destination_n * destination_n_1 = p_destination_tmp;						
						p_destination_tmp = p_destination_tmp->next;

						MEM_free(destination_n_1);

					}

					/*
					if (tmp_ATS_list != NULL)
					{
						clear_tco_node_addr_set(&tmp_ATS_list);
					}
					*/
					

				}
				else
				{
					//mean perfect +0 chg for TS
				}
			}
		}


		if (p_list_destination_ats != NULL && p_list_destination_ats2 == NULL)
		{
			p_list_destination_ats2 = p_list_destination_ats;
		}

		UInt32 uiInnerExchangeLUCnt = 0;

		//SubFuncForLoopHelpFuncV22(node, (&e2_plus_one.list_p0), NULL, NULL, &e2_plus_two, &uiInnerExchangeLUCnt, &ATS_list, &disconnected_list);
		SubFuncForLoopHelpFuncV22(node, (&e2_plus_one.list_p0), NULL, NULL, &e2_plus_two, &uiInnerExchangeLUCnt, &ATS_list, &disconnected_list);

		if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
		{
			uiLookupCnt += uiInnerExchangeLUCnt;
		}


		//deal with children of list_destination_TS_plus_one_p0

		uiInnerExchangeLUCnt = 0;

		if (g_iToAchieveSameRoute == 1)
		{
			
			destination_n* list_avoid_consider_for_p1 = NULL;
			tco_node_addr* tco_avoid_consider_list_p1 = NULL;


			//p1 list, +0 exchange
			if (e2_plus_two.list_p1 != NULL)
			{

				while (e2_plus_two.list_p1 != NULL)
				{

					destination_n* destination_n_1 = NULL;
					destination_list* topo_dest = NULL;
					
					
					if (e2_plus_two.list_p1->bChildrenDetermined)
					{
						destination_n * dst_child = e2_plus_two.list_p1->children;
						while (dst_child != NULL)
						{


							Address addrReached = dst_child->destination->rt_entry_infos.rtu_dst;							

							UInt32 uiInnerExchangeLUCnt = 0;

							OlsrCalculateRoutingTableForSinglePathTopologySearchHelpFuncV24(node, dst_child, addrReached, e2_plus_two.list_p1, &e2_plus_two.list_p0, 
								&list_avoid_consider_for_p1, &uiInnerExchangeLUCnt, &tco_avoid_consider_list_p1, &ATS_list, &disconnected_list);

							dst_child = dst_child->next;
						}
					}
					else
					{
						topology_last_entry* topo_last = OlsrLookupLastTopologyTableSYM(node, e2_plus_two.list_p1->destination->rt_dst);


						if (NULL != topo_last)
						{
							topo_dest = topo_last->topology_list_of_destinations;

							while (topo_dest != NULL)
							{

								Address addrReached = topo_dest->destination_node->topology_destination_dst;							

								UInt32 uiInnerExchangeLUCnt = 0;

								OlsrCalculateRoutingTableForSinglePathTopologySearchHelpFuncV24(node, NULL, addrReached, e2_plus_two.list_p1, &e2_plus_two.list_p0, 
									&list_avoid_consider_for_p1, &uiInnerExchangeLUCnt, &tco_avoid_consider_list_p1, &ATS_list, &disconnected_list);

								topo_dest = topo_dest->next;
							}
						}
					}
										

					destination_n_1 = e2_plus_two.list_p1;
					e2_plus_two.list_p1 = e2_plus_two.list_p1->next;
					MEM_free(destination_n_1);
				}


			}




			if (list_avoid_consider_for_p1 != NULL)
			{

				while (list_avoid_consider_for_p1 != NULL)
				{

					destination_n* destination_n_1 = NULL;

					if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
					{
						uiLookupCnt++;
					}


					//while (topo_dest != NULL)
					{

						Address addrReached = list_avoid_consider_for_p1->destination->rt_dst;

						UInt32 uiInnerExchangeLUCnt = 0;

						rt_entry* preExisting = list_avoid_consider_for_p1->destination;


						preExisting->rt_entry_infos.bCostChanged = FALSE;
						preExisting->rt_entry_infos.bDescendentRequireFurtherUpdate = FALSE;
						preExisting->rt_entry_infos.bRequireDelete = FALSE;

						preExisting->rt_entry_infos.uiCostChg = 0;


						BOOL bExchangeFound = FindRouteExchangeV21(node, list_avoid_consider_for_p1, preExisting, TRUE, NULL, &uiInnerExchangeLUCnt, FALSE, &tco_avoid_consider_list_p1, &ATS_list, 
							&disconnected_list, &ATS_list_backup, &disconnected_list_backup);
						
						if (!bExchangeFound)
						{

							//should certainly find

						}
						else
						{
							if (preExisting->rt_entry_infos.bDescendentRequireFurtherUpdate)
							{

								destination_n* list_destination_tmp;
								list_destination_tmp = (destination_n* )
									MEM_malloc(sizeof(destination_n));

								memset(
									list_destination_tmp,
									0,
									sizeof(destination_n));

								//list_destination_tmp->destination = preExisting;

								list_destination_tmp->destination = preExisting;

								{
									list_destination_tmp->children = list_avoid_consider_for_p1->children;
									list_destination_tmp->bChildrenDetermined = list_avoid_consider_for_p1->bChildrenDetermined;

									list_avoid_consider_for_p1->children = NULL;
								}

								list_destination_tmp->next = e2_plus_three.list_p1;
								e2_plus_three.list_p1 = list_destination_tmp;


								//+1 case								

							}

						}



						//Peter Added for test time complexity
						if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
						{
							uiLookupCnt += uiInnerExchangeLUCnt;

							//if (node->nodeId == NODE_ID_FOR_TEST_OUTER_ANGLE || node->nodeId == NODE_ID_FOR_TEST_OUTER_EDGE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_ANGLE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_EDGE || node->nodeId == NODE_ID_FOR_TEST_CENTER)
							if (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END)
							{
								uiLookupCnt++;

							}
						}

					}



					destination_n_1 = list_avoid_consider_for_p1;
					list_avoid_consider_for_p1 = list_avoid_consider_for_p1->next;


					remove_from_tco_node_addr_set(&tco_avoid_consider_list_p1, destination_n_1->destination->rt_entry_infos.rtu_dst.interfaceAddr.ipv4);

					MEM_free(destination_n_1);


				}

			}


			clear_tco_node_addr_set(&tco_avoid_consider_list_p1);
			
		}
		else
		{

			SubFuncForLoopHelpFuncV22(node, (&e2_plus_two.list_p1), &e2_plus_one, &e2_plus_two, &e2_plus_three, &uiInnerExchangeLUCnt, &ATS_list, &disconnected_list);

			//SubFuncForLoopHelpFuncV22(node, (&e2_s_n.list_p1), NULL, &e2_s_n, &e2_s_n_1, &uiInnerExchangeLUCnt);
		}



		
		if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
		{
			uiLookupCnt += uiInnerExchangeLUCnt;
		}


		if (g_iSpecailDebug == 1)
		{

			printf("\n-------------------------------- Special Debug Before +2 exchange  ----------------------------");


			SpecialDebug(node, DEBUG_NODE_ID, DEBUG_ENTRY_ID);


		}

		

		destination_n * p_list_destination_dts4 = NULL;
		{

			// need to find whether DATS can be exchanged by +2, since all +1 (till list_destination_TS_plus_two) are determined

			//tco_node_addr * tmp_disconnected_list = NULL;

			if (disconnected_list != NULL)
			{

				//while (disconnected_list != NULL)
				{

					//copy the set

					/*
					tco_node_addr * tmp_addr = disconnected_list;
					while (tmp_addr != NULL)
					{

						insert_into_tco_node_addr_set(&(tmp_disconnected_list), tmp_addr->nid);
						tmp_addr = tmp_addr->next;
					}

					tco_node_addr * tmp_addr_tmp = tmp_disconnected_list;
					*/

					//BOOL bAtleastFindOne = FALSE;

					destination_n * p_destination_tmp = p_list_destination_dts3;
					while (p_destination_tmp != NULL)
					{

						rt_entry* prte = p_destination_tmp->destination;

						if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
						{
							uiLookupCnt++;
						}

						if (prte != NULL)
						{

							//the exchange here need to support unconsider set,
							//to avoid circular dependency 

							prte->rt_entry_infos.uiCostChg = 0;

							prte->rt_entry_infos.bCostChanged = FALSE;
							prte->rt_entry_infos.bDescendentRequireFurtherUpdate = FALSE;
							prte->rt_entry_infos.bRequireDelete = FALSE;


							BOOL bExchangeFound = FindRouteExchangeV22(node, p_destination_tmp, prte, FALSE, NULL, &uiLookupCnt, FALSE, &ATS_list, &disconnected_list, &ATS_list_backup, &disconnected_list_backup);
							if (!bExchangeFound)
							{

								destination_n* list_destination_tmp;
								list_destination_tmp = (destination_n* )
									MEM_malloc(sizeof(destination_n));

								memset(
									list_destination_tmp,
									0,
									sizeof(destination_n));

								list_destination_tmp->destination = prte;

								{
									list_destination_tmp->children = p_destination_tmp->children;
									list_destination_tmp->bChildrenDetermined = p_destination_tmp->bChildrenDetermined;

									p_destination_tmp->children = NULL;
								}


								list_destination_tmp->next = p_list_destination_dts4;
								p_list_destination_dts4 = list_destination_tmp;
							}
							else
							{

								remove_from_tco_node_addr_set(&(disconnected_list), prte->rt_entry_infos.rtu_dst.interfaceAddr.ipv4);
								//insert_into_tco_node_addr_set(&(found_list), tmp_addr_tmp->nid);

								//bAtleastFindOne = TRUE;

								if (prte->rt_entry_infos.bDescendentRequireFurtherUpdate)
								{

									if (prte->rt_entry_infos.uiCostChg == 2)
									{
										destination_n* list_destination_tmp;
										list_destination_tmp = (destination_n* )
											MEM_malloc(sizeof(destination_n));

										memset(
											list_destination_tmp,
											0,
											sizeof(destination_n));

										list_destination_tmp->destination = prte;

										{
											list_destination_tmp->children = p_destination_tmp->children;
											list_destination_tmp->bChildrenDetermined = p_destination_tmp->bChildrenDetermined;

											p_destination_tmp->children = NULL;
										}


										list_destination_tmp->next = e2_plus_three.list_p2;
										e2_plus_three.list_p2 = list_destination_tmp;

									}
									else
									{
										//should not happen
									}

								}
								else
								{
									//perfect exchange
									//should not happen
								}

							}
						}

						//tmp_addr_tmp = tmp_addr_tmp->next;

						destination_n * destination_n_1 = p_destination_tmp;						
						p_destination_tmp = p_destination_tmp->next;

						MEM_free(destination_n_1);
					}


					/*
					if (tmp_disconnected_list != NULL)
					{
						clear_tco_node_addr_set(&tmp_disconnected_list);
					}
					*/

				}


			}
			else
			{
				//
			}


		}


		destination_n * p_list_destination_ats3 = NULL;
		{

			// need to find whether ATS can be exchanged by +2, since all +1 (till list_destination_TS_plus_two) are determined

			//tco_node_addr * tmp_ATS_list = NULL;

			if (ATS_list != NULL)
			{

				//while (disconnected_list != NULL)
				{

					//copy the set

					/*
					tco_node_addr * tmp_addr = ATS_list;
					while (tmp_addr != NULL)
					{

						insert_into_tco_node_addr_set(&(tmp_ATS_list), tmp_addr->nid);
						tmp_addr = tmp_addr->next;
					}

					tco_node_addr * tmp_addr_tmp = tmp_ATS_list;
					*/

					//BOOL bAtleastFindOne = FALSE;
					destination_n * p_destination_tmp = p_list_destination_ats2;
					while (p_destination_tmp != NULL)
					{

						rt_entry* prte = p_destination_tmp->destination;

						if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
						{
							uiLookupCnt++;
						}

						if (prte != NULL)
						{

							//the exchange here need to support unconsider set,
							//to avoid circular dependency 

							prte->rt_entry_infos.uiCostChg = 0;

							prte->rt_entry_infos.bCostChanged = FALSE;
							prte->rt_entry_infos.bDescendentRequireFurtherUpdate = FALSE;
							prte->rt_entry_infos.bRequireDelete = FALSE;


							BOOL bExchangeFound = FALSE;

							if (g_iToAchieveSameRoute == 1)
							{

								if (bExistReachTCFromTDNodeTBD && prteTC->rt_entry_infos.bDescendentRequireFurtherUpdate && prteTC->rt_entry_infos.uiCostChg == 2)
								{
									bExchangeFound = FindRouteExchangeV22(node, p_destination_tmp, prte, TRUE, NULL, &uiLookupCnt, FALSE, &ATS_list, &disconnected_list, &ATS_list_backup, &disconnected_list_backup);
								}
								else
								{
									bExchangeFound = FindRouteExchangeV22(node, p_destination_tmp, prte, FALSE, NULL, &uiLookupCnt, FALSE, &ATS_list, &disconnected_list, &ATS_list_backup, &disconnected_list_backup);
								}							

							}
							else
							{
								bExchangeFound = FindRouteExchangeV22(node, p_destination_tmp, prte, FALSE, NULL, &uiLookupCnt, FALSE, &ATS_list, &disconnected_list, &ATS_list_backup, &disconnected_list_backup);

							}

							
							if (!bExchangeFound)
							{
						
								destination_n* list_destination_tmp;
								list_destination_tmp = (destination_n* )
									MEM_malloc(sizeof(destination_n));

								memset(
									list_destination_tmp,
									0,
									sizeof(destination_n));

								list_destination_tmp->destination = prte;

								{
									list_destination_tmp->children = p_destination_tmp->children;
									list_destination_tmp->bChildrenDetermined = p_destination_tmp->bChildrenDetermined;

									p_destination_tmp->children = NULL;
								}


								list_destination_tmp->next = p_list_destination_ats3;
								p_list_destination_ats3 = list_destination_tmp;
								
							}
							else
							{

								remove_from_tco_node_addr_set(&(ATS_list), prte->rt_entry_infos.rtu_dst.interfaceAddr.ipv4);
								//insert_into_tco_node_addr_set(&(found_list), tmp_addr_tmp->nid);

								//bAtleastFindOne = TRUE;
								if (prte->rt_entry_infos.bDescendentRequireFurtherUpdate)
								{

									if (prte->rt_entry_infos.uiCostChg == 2)
									{
										destination_n* list_destination_tmp;
										list_destination_tmp = (destination_n* )
											MEM_malloc(sizeof(destination_n));

										memset(
											list_destination_tmp,
											0,
											sizeof(destination_n));

										list_destination_tmp->destination = prte;

										{
											list_destination_tmp->children = p_destination_tmp->children;
											list_destination_tmp->bChildrenDetermined = p_destination_tmp->bChildrenDetermined;

											p_destination_tmp->children = NULL;
										}


										list_destination_tmp->next = e2_plus_three.list_p2;
										e2_plus_three.list_p2 = list_destination_tmp;

									}
									else
									{
										//should not happen
									}

								}
								else
								{
									//perfect exchange
									//should not happen
								}

							}
						}

						//tmp_addr_tmp = tmp_addr_tmp->next;

						destination_n * destination_n_1 = p_destination_tmp;						
						p_destination_tmp = p_destination_tmp->next;

						MEM_free(destination_n_1);
					}


					/*
					if (tmp_ATS_list != NULL)
					{
						clear_tco_node_addr_set(&tmp_ATS_list);
					}
					*/

				}


			}
			else
			{
				//
			}


		}


		clear_tco_node_addr_set(&ATS_list_backup);
		clear_tco_node_addr_set(&disconnected_list_backup);

		

		if (g_iSpecailDebug == 1)
		{

			printf("\n-------------------------------- Special Debug After +2 exchange  ----------------------------");


			SpecialDebug(node, DEBUG_NODE_ID, DEBUG_ENTRY_ID);


		}

		
		//if ATS_list or disconnected_list is still NOT NULL, then consider it can not find exchange and has to be deleted
		//tco_node_addr * tna_tmp = NULL;

		//tna_tmp = ATS_list;
		destination_n * p_destination_tmp = p_list_destination_ats3;
		while (p_destination_tmp != NULL)
		{

			//rt_entry* prte = QueryRoutingTableAccordingToNodeId(node, tna_tmp->nid);
			rt_entry* prte = p_destination_tmp->destination;

			prte->rt_metric = MAX_COST;


			destination_n* list_destination_tmp;
			list_destination_tmp = (destination_n* )
				MEM_malloc(sizeof(destination_n));

			memset(
				list_destination_tmp,
				0,
				sizeof(destination_n));

			list_destination_tmp->destination = prte;


			{
				list_destination_tmp->children = p_destination_tmp->children;
				list_destination_tmp->bChildrenDetermined = p_destination_tmp->bChildrenDetermined;

				p_destination_tmp->children = NULL;
			}



			list_destination_tmp->next = e2_plus_one.list_delete;
			e2_plus_one.list_delete = list_destination_tmp;

			destination_n * destination_n_1 = p_destination_tmp;						
			p_destination_tmp = p_destination_tmp->next;

			MEM_free(destination_n_1);
		}

		clear_tco_node_addr_set(&ATS_list);



		//tna_tmp = disconnected_list;
		p_destination_tmp = p_list_destination_dts4;
		while (p_destination_tmp != NULL)
		{

			//rt_entry* prte = QueryRoutingTableAccordingToNodeId(node, tna_tmp->nid);

			rt_entry* prte = p_destination_tmp->destination;

			prte->rt_metric = MAX_COST;


			destination_n* list_destination_tmp;
			list_destination_tmp = (destination_n* )
				MEM_malloc(sizeof(destination_n));

			memset(
				list_destination_tmp,
				0,
				sizeof(destination_n));

			list_destination_tmp->destination = prte;


			{
				list_destination_tmp->children = p_destination_tmp->children;
				list_destination_tmp->bChildrenDetermined = p_destination_tmp->bChildrenDetermined;

				p_destination_tmp->children = NULL;
			}



			list_destination_tmp->next = e2_plus_one.list_delete;
			e2_plus_one.list_delete = list_destination_tmp;

			destination_n * destination_n_1 = p_destination_tmp;						
			p_destination_tmp = p_destination_tmp->next;

			MEM_free(destination_n_1);
		}

		clear_tco_node_addr_set(&disconnected_list);



		if (e2_plus_zero.list_delete != NULL)
		{

			destination_n* destination_n_1 = NULL;

			destination_n_1 = e2_plus_zero.list_delete;
			e2_plus_zero.list_delete = e2_plus_zero.list_delete->next;


			destination_n_1->destination->rt_metric = MAX_COST;

			insert_into_tco_node_addr_set(&olsr->recent_add_list, destination_n_1->destination->rt_entry_infos.rtu_dst.interfaceAddr.ipv4);

			//MEM_free(destination_n_1);
			//add to delete entry list without real delete
			destination_n_1->next = list_destination_delete;
			list_destination_delete = destination_n_1;
		

		}


		//construct the delete list till e2_plus_two.list_delete;

		DeleteListProgress(node, &e2_plus_one, &e2_plus_two, &olsr->recent_add_list, &list_destination_delete);


		DeleteListProgress(node, &e2_plus_two, &e2_plus_three, &olsr->recent_add_list, &list_destination_delete);

	


		//destination_n * list_n_minus_1_p0 = NULL;

		tco_node_addr * tco_avoid_consider_list = NULL;
		destination_n * list_avoid_consider_for_p2 = NULL;



		
		if (g_iSpecailDebug == 1)
		{

			printf("\n-------------------------------- Special Debug Before SubFuncForLoopHelpFuncV23 ----------------------------");


			SpecialDebug(node, DEBUG_NODE_ID, DEBUG_ENTRY_ID);


		}


		uiInnerExchangeLUCnt = 0;
		SubFuncForLoopHelpFuncV23(node, e2_plus_three, &e2_plus_two.list_p0, &list_avoid_consider_for_p2, &uiInnerExchangeLUCnt, &tco_avoid_consider_list);

		if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
		{
			uiLookupCnt += uiInnerExchangeLUCnt;
		}
		
		
		if (g_iSpecailDebug == 1)
		{

			printf("\n-------------------------------- Special Debug Before SubFuncForLoopHelpFuncV22 ----------------------------");


			SpecialDebug(node, DEBUG_NODE_ID, DEBUG_ENTRY_ID);


		}



		uiInnerExchangeLUCnt = 0;

		SubFuncForLoopHelpFuncV22(node, (&e2_plus_two.list_p0), NULL, NULL, &e2_plus_three, &uiInnerExchangeLUCnt, &tco_avoid_consider_list);

		if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
		{
			uiLookupCnt += uiInnerExchangeLUCnt;
		}

	
		if (g_iSpecailDebug == 1)
		{

			printf("\n-------------------------------- Special Debug Before ProcessRecurrentPlus2 ----------------------------");


			SpecialDebug(node, DEBUG_NODE_ID, DEBUG_ENTRY_ID);

			
		}


		ProcessRecurrentPlus2(node, uiTCOldCost + 3, &tco_avoid_consider_list, &olsr->recent_add_list, e2_plus_three, &list_avoid_consider_for_p2, &list_destination_delete, &uiLookupCnt);

		
		if (g_iSpecailDebug == 1)
		{

			printf("\n-------------------------------- Special Debug After ProcessRecurrentPlus2 ----------------------------");


			SpecialDebug(node, DEBUG_NODE_ID, DEBUG_ENTRY_ID);


		}


		//start the recurrent exchange & delete

		/*
		//e2_s e2_plus_zero;
		//e2_s e2_s_n_minus_1;
		e2_s e2_s_n;
		e2_s e2_s_n_1;


		//e2_s_n_minus_1.list_delete = e2_plus_two.list_delete;
		//e2_s_n_minus_1.list_p0 = e2_plus_two.list_p0;
		//e2_s_n_minus_1.list_p1 = e2_plus_two.list_p1;
		//e2_s_n_minus_1.list_p2 = e2_plus_two.list_p2;


		e2_s_n.list_delete = e2_plus_three.list_delete;
		e2_s_n.list_p0 = e2_plus_three.list_p0;
		e2_s_n.list_p1 = e2_plus_three.list_p1;
		e2_s_n.list_p2 = e2_plus_three.list_p2;

		e2_s_n_1.list_delete = e2_s_n.list_delete;
		e2_s_n_1.list_p0 = e2_s_n.list_p0;
		e2_s_n_1.list_p1 = e2_s_n.list_p1;
		e2_s_n_1.list_p2 = e2_s_n.list_p2;
		*/



	



		clear_tco_node_addr_set(&tco_avoid_consider_list);


		//clear_tco_node_addr_set(&ATS_list);
		//clear_tco_node_addr_set(&disconnected_list);


	}
	else
	{
		//process for delete is not required 
	}


	//return NULL;
	return list_destination_delete;	
}



//try a simple way, such that just delete all and use the add-list method to regional re-discovery
destination_n* ProcessRoutingTableAccordingToRecentDeleteListV33(Node* node, BOOL * pbRequireRediscovery, UInt32 * puiLookupCntForDeleteList)
{

	//now we just try a strict standard that only allow 

	//great
	destination_n * list_destination_n = NULL;



	RoutingOlsr * olsr = (RoutingOlsr *) node->appData.olsr;

	tco_node_addr * tco_delete_list_tmp = olsr->recent_delete_list;			

	UInt32 uiLookupCnt = 0;

	if (pbRequireRediscovery != NULL)
	{
		*pbRequireRediscovery = FALSE;
	}
	

	tco_node_addr * disconnected_list = NULL;
	
	//tco_node_addr * deleted_list = NULL;

	if (olsr->recent_add_list != NULL)
	{
		clear_tco_node_addr_set(&olsr->recent_add_list);
	}


	rt_entry* prteTC = QueryRoutingTableAccordingToNodeId(node, olsr->naRecentChangedAddressByTC);
	if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
	{
		uiLookupCnt++;
	}

	if (prteTC != NULL)
	{
		BOOL bExistReachTCFromTDNodeTBD = FALSE;

		/*
		prteTC->rt_entry_infos.bDescendentRequireFurtherUpdate = FALSE;
		prteTC->rt_entry_infos.bCostChanged = FALSE;
		prteTC->rt_entry_infos.bRequireDelete = FALSE;
		*/


		while (tco_delete_list_tmp != NULL)
		{

			if (prteTC->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 == tco_delete_list_tmp->nid)
			{

				if (prteTC->rt_metric == 2)
				{

					BOOL b2HopNeighborCausedConnection = FALSE;
					b2HopNeighborCausedConnection = ConnectivetyCausedBy2HopNeighbor(node, prteTC->rt_entry_infos.rtu_dst, tco_delete_list_tmp->nid);

					if (b2HopNeighborCausedConnection)
					{

						remove_from_tco_node_addr_set(&(olsr->recent_delete_list), tco_delete_list_tmp->nid);

						break;
					}										
				}



				bExistReachTCFromTDNodeTBD = TRUE;

				remove_from_tco_node_addr_set(&(olsr->recent_delete_list), tco_delete_list_tmp->nid);


				break;
			}

			tco_delete_list_tmp = tco_delete_list_tmp->next;
		}


		

		if (bExistReachTCFromTDNodeTBD)
		{

			//delete all the descendants of TC node
			insert_into_tco_node_addr_set(&(disconnected_list), olsr->naRecentChangedAddressByTC);
			

			OlsrDeleteRoutingTable(prteTC);

			insert_into_tco_node_addr_set(&(olsr->recent_add_list), olsr->naRecentChangedAddressByTC);
		}
		
		//this should be anyway, regardless of whether bExistReachTCFromTDNodeTBD is true or false
		{
			//further check the DATS nodes
			

			//int iDisconnectCount = 0;

			tco_delete_list_tmp = olsr->recent_delete_list;

			while (tco_delete_list_tmp != NULL)
			{

				rt_entry* prte = QueryRoutingTableAccordingToNodeId(node, tco_delete_list_tmp->nid);

				if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
				{
					uiLookupCnt++;
				}

				if (prte != NULL)
				{

					if (prte->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 == olsr->naRecentChangedAddressByTC)
					{

						if (prte->rt_metric == 2)
						{
							BOOL b2HopNeighborCausedConnection = FALSE;

							b2HopNeighborCausedConnection = ConnectivetyCausedBy2HopNeighbor(node, prte->rt_entry_infos.rtu_dst, olsr->naRecentChangedAddressByTC);
							if (b2HopNeighborCausedConnection)
							{

								//remove_from_tco_node_addr_set(&(olsr->recent_delete_list), tco_delete_list_tmp->nid);

								tco_delete_list_tmp = tco_delete_list_tmp->next;

								continue;
							}
						}

						insert_into_tco_node_addr_set(&(disconnected_list), tco_delete_list_tmp->nid);

						OlsrDeleteRoutingTable(prte);

						
						insert_into_tco_node_addr_set(&(olsr->recent_add_list), tco_delete_list_tmp->nid);
						

					}
					else
					{
						//it is possible that nodes can be reached but not consider TCNode as last hop
						//skip these nodes

					}

				}
				else
				{

					//should not happen
				}


				tco_delete_list_tmp = tco_delete_list_tmp->next;
			}

		}

		


		tco_node_addr * destination_list_n_1 = disconnected_list;
		tco_node_addr * destination_list_n = disconnected_list;

		while (destination_list_n_1 != NULL)
		{

			destination_list_n_1 = NULL;

			topology_last_entry* topo_last = NULL;
			destination_list* topo_dest = NULL;


			//Peter comment: every loop add group of destination nodes that one hop more from the source node,
			//compare to the group in the previous loop  
			while (destination_list_n != NULL)
			{
				tco_node_addr* tna_tmp = NULL;

				Address addrCurrent;
				addrCurrent.networkType = NETWORK_IPV4;
				addrCurrent.interfaceAddr.ipv4 = destination_list_n->nid;

				//Peter comment: find from the topology table if there is some entry 
				//whose last hop equal the specific dest hop of 2 or more (* since every loop will
				// increase the one more hop count) hop neighbors
				if (SYMMETRIC_TOPOLOGY_TABLE)
				{
					topo_last = OlsrLookupLastTopologyTableSYM(node, addrCurrent);
				}
				else
				{
					topo_last = OlsrLookupLastTopologyTable(node, addrCurrent);
				}


				if (NULL != topo_last)
				{
					topo_dest = topo_last->topology_list_of_destinations;

					while (topo_dest != NULL)
					{

						Address addrReached = topo_dest->destination_node->topology_destination_dst;

					
						rt_entry* prte_tmp = QueryRoutingTableAccordingToNodeId(node, addrReached.interfaceAddr.ipv4);
						
						if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
						{
							uiLookupCnt++;
						}

						if (prte_tmp != NULL)
						{
							 if (prte_tmp->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 == destination_list_n->nid)
							 {
								 insert_into_tco_node_addr_set(&(destination_list_n_1), addrReached.interfaceAddr.ipv4);
								 
								 OlsrDeleteRoutingTable(prte_tmp);

								 insert_into_tco_node_addr_set(&(olsr->recent_add_list), addrReached.interfaceAddr.ipv4);

							 }
						}				
						

						topo_dest = topo_dest->next;
					}
				}

				tna_tmp = destination_list_n;
				destination_list_n = destination_list_n->next;
				MEM_free(tna_tmp);
			}

			destination_list_n = destination_list_n_1;
		
		}


	}
	else
	{
		//process for delete is not required 
	}


	if (olsr->recent_add_list != NULL)
	{
		UInt32 uiLC = 0;

		destination_n* list_destination_n_1 = NULL;
		list_destination_n_1 = ProcessRoutingTableAccordingToRecentAddListV2(node, &uiLC);

		
		if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
		{
			//uiLookupCnt++;
			uiLookupCnt += uiLC;
		}

		//list_destination_n = list_destination_n_1

		if (list_destination_n_1 != NULL)
		{

			list_destination_n = list_destination_n_1;

			while (list_destination_n_1 != NULL)
			{
				list_destination_n_1 = NULL;

				destination_n*  tmp_destination_tail = NULL;

				topology_last_entry* topo_last = NULL;
				destination_list* topo_dest = NULL;

				//Peter comment: every loop add group of destination nodes that one hop more from the source node,
				//compare to the group in the previous loop  
				while (list_destination_n != NULL)
				{
					destination_n* destination_n_1 = NULL;

					if (DEBUG)
					{
						char addrString[MAX_STRING_LENGTH];

						IO_ConvertIpAddressToString(
							&list_destination_n->destination->rt_dst,
							addrString);

						printf("Node %d, Last hop %s\n",
							node->nodeId,
							addrString);
					}

					//Peter comment: find from the topology table if there is some entry 
					//whose last hop equal the specific dest hop of 2 or more (* since every loop will
					// increase the one more hop count) hop neighbors
					if (SYMMETRIC_TOPOLOGY_TABLE)
					{
						topo_last = OlsrLookupLastTopologyTableSYM(node, list_destination_n->destination->rt_dst);
					}
					else
					{
						topo_last = OlsrLookupLastTopologyTable(node, list_destination_n->destination->rt_dst);
					}


					if (NULL != topo_last)
					{
						topo_dest = topo_last->topology_list_of_destinations;


						while (topo_dest != NULL)
						{

							Address addrReached = topo_dest->destination_node->topology_destination_dst;

							if (RoutingOlsrCheckMyIfaceAddress(
								node,
								topo_dest->destination_node->topology_destination_dst) != -1)
							{
								topo_dest = topo_dest->next;
								continue;
							}


							OlsrCalculateRoutingTableForSinglePathTopologySearchHelpFunc(node, addrReached, list_destination_n, &list_destination_n_1, &tmp_destination_tail, TRUE);


							//Peter Added for test time complexity
							if (_TEST_TIME_COMPLEXITY)
							{

								//if (node->nodeId == NODE_ID_FOR_TEST_OUTER_ANGLE || node->nodeId == NODE_ID_FOR_TEST_OUTER_EDGE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_ANGLE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_EDGE || node->nodeId == NODE_ID_FOR_TEST_CENTER)
								if (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END)
								{
									uiLookupCnt++;

								}
							}

							topo_dest = topo_dest->next;
						}
					}

					destination_n_1 = list_destination_n;
					list_destination_n = list_destination_n->next;
					MEM_free(destination_n_1);
				}

				list_destination_n = list_destination_n_1;
				//ui_metric_cost_limitation++;
			}
		}

	}
	else
	{

	}

	if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
	{
		//uiLookupCnt++;
		*puiLookupCntForDeleteList = uiLookupCnt;
	}


	//return NULL;
	return list_destination_n;	


}


//try a simple way, such that use the delete-list (formed by earlier stage of ProcessRoutingTableAccordingToRecentAddListV42) and use the add-list method to regional re-discovery
destination_n* ProcessRoutingTableAccordingToRecentDeleteListV44(Node* node, BOOL * pbRequireRediscovery, destination_n ** plist_destination_delete, UInt32 * puiLookupCntForDeleteList)
{

	//now we just try a strict standard that only allow 

	//great
	destination_n * list_destination_n = NULL;



	RoutingOlsr * olsr = (RoutingOlsr *) node->appData.olsr;

	tco_node_addr * tco_delete_list_tmp = olsr->recent_delete_list;			

	UInt32 uiLookupCnt = 0;

	*pbRequireRediscovery = FALSE;

	tco_node_addr * disconnected_list = NULL;

	//tco_node_addr * deleted_list = NULL;


	


	/*
	if (!exist_in_tco_node_addr_set(&olsr->recent_delete_list, olsr->naRecentChangedAddressByTC))
	{
		//this should never happen

		return list_destination_n;
	}


	if (olsr->recent_add_list != NULL)
	{
		clear_tco_node_addr_set(&olsr->recent_add_list);
	}


	rt_entry* prteTC = QueryRoutingTableAccordingToNodeId(node, olsr->naRecentChangedAddressByTC);
	if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
	{
		uiLookupCnt++;
	}


	if (prteTC != NULL)
	{

		OlsrDeleteRoutingTable(prteTC);

		insert_into_tco_node_addr_set(&(olsr->recent_add_list), olsr->naRecentChangedAddressByTC);


		ProcessRoutingTableAccordingToSpecificRoute(node, olsr->naRecentChangedAddressByTC);


	}
	else
	{
		//process for delete is not required 

		//return list_destination_n;
	}
	*/


	if (olsr->recent_delete_list != NULL)
	{
		UInt32 uiLC = 0;

		destination_n* list_destination_n_1 = NULL;
		list_destination_n_1 = ProcessRoutingTableAccordingToRecentAddListV2(node, &uiLC, &olsr->recent_delete_list, plist_destination_delete);


		if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
		{
			//uiLookupCnt++;
			uiLookupCnt += uiLC;
		}

		//list_destination_n = list_destination_n_1

		if (list_destination_n_1 != NULL)
		{

			list_destination_n = list_destination_n_1;

			while (list_destination_n_1 != NULL)
			{
				list_destination_n_1 = NULL;
				destination_n*  tmp_destination_tail = NULL;

				topology_last_entry* topo_last = NULL;
				destination_list* topo_dest = NULL;

				//Peter comment: every loop add group of destination nodes that one hop more from the source node,
				//compare to the group in the previous loop  
				while (list_destination_n != NULL)
				{
					destination_n* destination_n_1 = NULL;

					if (DEBUG)
					{
						char addrString[MAX_STRING_LENGTH];

						IO_ConvertIpAddressToString(
							&list_destination_n->destination->rt_dst,
							addrString);

						printf("Node %d, Last hop %s\n",
							node->nodeId,
							addrString);
					}

					//Peter comment: find from the topology table if there is some entry 
					//whose last hop equal the specific dest hop of 2 or more (* since every loop will
					// increase the one more hop count) hop neighbors
					if (SYMMETRIC_TOPOLOGY_TABLE)
					{
						topo_last = OlsrLookupLastTopologyTableSYM(node, list_destination_n->destination->rt_dst);
					}
					else
					{
						topo_last = OlsrLookupLastTopologyTable(node, list_destination_n->destination->rt_dst);
					}


					if (NULL != topo_last)
					{
						topo_dest = topo_last->topology_list_of_destinations;


						while (topo_dest != NULL)
						{

							Address addrReached = topo_dest->destination_node->topology_destination_dst;

							if (RoutingOlsrCheckMyIfaceAddress(
								node,
								topo_dest->destination_node->topology_destination_dst) != -1)
							{
								topo_dest = topo_dest->next;
								continue;
							}


							OlsrCalculateRoutingTableForSinglePathTopologySearchHelpFunc(node, addrReached, list_destination_n, &list_destination_n_1, &tmp_destination_tail, TRUE);


							//Peter Added for test time complexity
							if (_TEST_TIME_COMPLEXITY)
							{

								//if (node->nodeId == NODE_ID_FOR_TEST_OUTER_ANGLE || node->nodeId == NODE_ID_FOR_TEST_OUTER_EDGE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_ANGLE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_EDGE || node->nodeId == NODE_ID_FOR_TEST_CENTER)
								if (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END)
								{
									uiLookupCnt++;

								}
							}

							topo_dest = topo_dest->next;
						}
					}

					destination_n_1 = list_destination_n;
					list_destination_n = list_destination_n->next;
					MEM_free(destination_n_1);
				}

				list_destination_n = list_destination_n_1;
				//ui_metric_cost_limitation++;
			}
		}

	}
	else
	{

	}

	if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
	{
		//uiLookupCnt++;
		*puiLookupCntForDeleteList = uiLookupCnt;
	}


	//return NULL;
	return list_destination_n;	


}




destination_n* ProcessRoutingTableAccordingToRecentDeleteListV53(Node* node, tco_node_addr ** tna_to_delete, UInt32 * puiLookupCntForDeleteList, destination_n * p_list_delete)
{

	//now we just try a strict standard that only allow 

	//great
	destination_n * list_destination_n = NULL;



	//RoutingOlsr * olsr = (RoutingOlsr *) node->appData.olsr;

	tco_node_addr * tco_delete_list_tmp = *tna_to_delete;			

	UInt32 uiLookupCnt = 0;

	//*pbRequireRediscovery = FALSE;

	tco_node_addr * disconnected_list = NULL;

	//tco_node_addr * deleted_list = NULL;


	/*
	if (!exist_in_tco_node_addr_set(&olsr->recent_delete_list, olsr->naRecentChangedAddressByTC))
	{
		//this should never happen

		return list_destination_n;
	}


	if (olsr->recent_add_list != NULL)
	{
		clear_tco_node_addr_set(&olsr->recent_add_list);
	}



	rt_entry* prteTC = QueryRoutingTableAccordingToNodeId(node, olsr->naRecentChangedAddressByTC);
	if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
	{
		uiLookupCnt++;
	}


	if (prteTC != NULL)
	{

		OlsrDeleteRoutingTable(prteTC);

		insert_into_tco_node_addr_set(&(olsr->recent_add_list), olsr->naRecentChangedAddressByTC);


		ProcessRoutingTableAccordingToSpecificRoute(node, olsr->naRecentChangedAddressByTC);


	}
	else
	{
		//process for delete is not required 

		//return list_destination_n;
	}
	*/


	//try to delete the delete list 
	//do not know why raise exception when move this segment after the ???
	
	//maybe the OlsrRemoveList((olsr_qelem *)destination) inside OlsrDeleteRoutingTable will 
	//be undetermined since the following update discovery will add new entries that modify the memory distribution
	
	/*
	while (p_list_delete != NULL)
	{
		destination_n* destination_n_1 = NULL;



		destination_n_1 = p_list_delete;
		p_list_delete = p_list_delete->next;


		if (destination_n_1 != NULL)
		{


			rt_entry* pdsttmp = NULL;

			pdsttmp = destination_n_1->destination;
		
			destination_n_1->destination = NULL;
			
			if (pdsttmp != NULL && pdsttmp->rt_metric == MAX_COST)
			{
				OlsrDeleteRoutingTable(pdsttmp);

				pdsttmp = NULL;
			}
		

			MEM_free(destination_n_1);
			destination_n_1 = NULL;
		
		}
	}
	*/
	
	
	

	if (tco_delete_list_tmp != NULL)
	{
		UInt32 uiLC = 0;

		destination_n* list_destination_n_1 = NULL;
		list_destination_n_1 = ProcessRoutingTableAccordingToRecentAddListV2(node, &uiLC, &tco_delete_list_tmp, &p_list_delete);


		if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
		{
			//uiLookupCnt++;
			uiLookupCnt += uiLC;
		}

		//list_destination_n = list_destination_n_1

		if (list_destination_n_1 != NULL)
		{

			list_destination_n = list_destination_n_1;

			while (list_destination_n_1 != NULL)
			{
				list_destination_n_1 = NULL;
				destination_n*  tmp_destination_tail = NULL;

				topology_last_entry* topo_last = NULL;
				destination_list* topo_dest = NULL;

				//Peter comment: every loop add group of destination nodes that one hop more from the source node,
				//compare to the group in the previous loop  
				while (list_destination_n != NULL)
				{
					destination_n* destination_n_1 = NULL;

					if (DEBUG)
					{
						char addrString[MAX_STRING_LENGTH];

						IO_ConvertIpAddressToString(
							&list_destination_n->destination->rt_dst,
							addrString);

						printf("Node %d, Last hop %s\n",
							node->nodeId,
							addrString);
					}

					//Peter comment: find from the topology table if there is some entry 
					//whose last hop equal the specific dest hop of 2 or more (* since every loop will
					// increase the one more hop count) hop neighbors
					if (SYMMETRIC_TOPOLOGY_TABLE)
					{
						topo_last = OlsrLookupLastTopologyTableSYM(node, list_destination_n->destination->rt_dst);
					}
					else
					{
						topo_last = OlsrLookupLastTopologyTable(node, list_destination_n->destination->rt_dst);
					}


					if (NULL != topo_last)
					{
						topo_dest = topo_last->topology_list_of_destinations;


						while (topo_dest != NULL)
						{

							Address addrReached = topo_dest->destination_node->topology_destination_dst;

							if (RoutingOlsrCheckMyIfaceAddress(
								node,
								topo_dest->destination_node->topology_destination_dst) != -1)
							{
								topo_dest = topo_dest->next;
								continue;
							}


							OlsrCalculateRoutingTableForSinglePathTopologySearchHelpFunc(node, addrReached, list_destination_n, &list_destination_n_1, &tmp_destination_tail, TRUE);


							//Peter Added for test time complexity
							if (_TEST_TIME_COMPLEXITY)
							{

								//if (node->nodeId == NODE_ID_FOR_TEST_OUTER_ANGLE || node->nodeId == NODE_ID_FOR_TEST_OUTER_EDGE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_ANGLE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_EDGE || node->nodeId == NODE_ID_FOR_TEST_CENTER)
								if (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END)
								{
									uiLookupCnt++;

								}
							}

							topo_dest = topo_dest->next;
						}
					}

					destination_n_1 = list_destination_n;
					list_destination_n = list_destination_n->next;
					MEM_free(destination_n_1);
				}

				list_destination_n = list_destination_n_1;
				//ui_metric_cost_limitation++;
			}
		}

	}
	else
	{

	}


	while (p_list_delete != NULL)
	{
		destination_n* destination_n_1 = NULL;



		destination_n_1 = p_list_delete;
		p_list_delete = p_list_delete->next;


		if (destination_n_1 != NULL)
		{


			rt_entry* pdsttmp = NULL;

			pdsttmp = destination_n_1->destination;

			destination_n_1->destination = NULL;

			if (pdsttmp != NULL && pdsttmp->rt_metric == MAX_COST)
			{
				OlsrDeleteRoutingTable(pdsttmp);

				pdsttmp = NULL;
			}


			MEM_free(destination_n_1);
			destination_n_1 = NULL;

		}
	}


	/*
	while (p_list_delete != NULL)
	{
		destination_n* destination_n_1 = NULL;



		destination_n_1 = p_list_delete;
		p_list_delete = p_list_delete->next;


		if (destination_n_1 != NULL)
		{


			rt_entry* pdsttmp = NULL;

			pdsttmp = destination_n_1->destination;

			destination_n_1->destination = NULL;

			if (pdsttmp != NULL && pdsttmp->rt_metric == MAX_COST)
			{
				//OlsrDeleteRoutingTable(pdsttmp);

				pdsttmp = NULL;
			}


			MEM_free(destination_n_1);
			destination_n_1 = NULL;

		}
	}
	*/
	

	


	if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
	{
		//uiLookupCnt++;
		*puiLookupCntForDeleteList = uiLookupCnt;
	}


	//return NULL;
	return list_destination_n;	


}



//try a simple way, such that just delete all and use the add-list method to regional re-discovery
destination_n* ProcessRoutingTableAccordingToRecentDeleteListV43(Node* node, BOOL * pbRequireRediscovery, destination_n ** plist_destination_delete, UInt32 * puiLookupCntForDeleteList)
{

	//now we just try a strict standard that only allow 

	//great
	destination_n * list_destination_n = NULL;



	RoutingOlsr * olsr = (RoutingOlsr *) node->appData.olsr;

	tco_node_addr * tco_delete_list_tmp = olsr->recent_delete_list;			

	UInt32 uiLookupCnt = 0;

	*pbRequireRediscovery = FALSE;

	tco_node_addr * disconnected_list = NULL;
	
	//tco_node_addr * deleted_list = NULL;


	if (!exist_in_tco_node_addr_set(&olsr->recent_delete_list, olsr->naRecentChangedAddressByTC))
	{
		//this should never happen
		
		return list_destination_n;
	}


	if (olsr->recent_add_list != NULL)
	{
		clear_tco_node_addr_set(&olsr->recent_add_list);
	}


	rt_entry* prteTC = QueryRoutingTableAccordingToNodeId(node, olsr->naRecentChangedAddressByTC);
	if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
	{
		uiLookupCnt++;
	}

	//destination_n* list_destination_delete = NULL;
	
	if (prteTC != NULL)
	{
	
		//OlsrDeleteRoutingTable(prteTC);

		//insert_into_tco_node_addr_set(&(olsr->recent_add_list), olsr->naRecentChangedAddressByTC);


		
		ProcessRoutingTableAccordingToSpecificRoute(node, olsr->naRecentChangedAddressByTC, plist_destination_delete);
	
		
	}
	else
	{
		//process for delete is not required 

		//return list_destination_n;
	}


	if (olsr->recent_add_list != NULL)
	{
		UInt32 uiLC = 0;

		destination_n* list_destination_n_1 = NULL;
		list_destination_n_1 = ProcessRoutingTableAccordingToRecentAddListV2(node, &uiLC, NULL, plist_destination_delete);

		
		if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
		{
			//uiLookupCnt++;
			uiLookupCnt += uiLC;
		}

		//list_destination_n = list_destination_n_1

		if (list_destination_n_1 != NULL)
		{

			list_destination_n = list_destination_n_1;

			while (list_destination_n_1 != NULL)
			{
				list_destination_n_1 = NULL;
				destination_n*  tmp_destination_tail = NULL;

				topology_last_entry* topo_last = NULL;
				destination_list* topo_dest = NULL;

				//Peter comment: every loop add group of destination nodes that one hop more from the source node,
				//compare to the group in the previous loop  
				while (list_destination_n != NULL)
				{
					destination_n* destination_n_1 = NULL;

					if (DEBUG)
					{
						char addrString[MAX_STRING_LENGTH];

						IO_ConvertIpAddressToString(
							&list_destination_n->destination->rt_dst,
							addrString);

						printf("Node %d, Last hop %s\n",
							node->nodeId,
							addrString);
					}

					//Peter comment: find from the topology table if there is some entry 
					//whose last hop equal the specific dest hop of 2 or more (* since every loop will
					// increase the one more hop count) hop neighbors
					if (SYMMETRIC_TOPOLOGY_TABLE)
					{
						topo_last = OlsrLookupLastTopologyTableSYM(node, list_destination_n->destination->rt_dst);
					}
					else
					{
						topo_last = OlsrLookupLastTopologyTable(node, list_destination_n->destination->rt_dst);
					}


					if (NULL != topo_last)
					{
						topo_dest = topo_last->topology_list_of_destinations;


						while (topo_dest != NULL)
						{

							Address addrReached = topo_dest->destination_node->topology_destination_dst;

							if (RoutingOlsrCheckMyIfaceAddress(
								node,
								topo_dest->destination_node->topology_destination_dst) != -1)
							{
								topo_dest = topo_dest->next;
								continue;
							}


							OlsrCalculateRoutingTableForSinglePathTopologySearchHelpFunc(node, addrReached, list_destination_n, &list_destination_n_1, &tmp_destination_tail, TRUE);


							//Peter Added for test time complexity
							if (_TEST_TIME_COMPLEXITY)
							{

								//if (node->nodeId == NODE_ID_FOR_TEST_OUTER_ANGLE || node->nodeId == NODE_ID_FOR_TEST_OUTER_EDGE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_ANGLE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_EDGE || node->nodeId == NODE_ID_FOR_TEST_CENTER)
								if (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END)
								{
									uiLookupCnt++;

								}
							}

							topo_dest = topo_dest->next;
						}
					}

					destination_n_1 = list_destination_n;
					list_destination_n = list_destination_n->next;
					MEM_free(destination_n_1);
				}

				list_destination_n = list_destination_n_1;
				//ui_metric_cost_limitation++;
			}
		}

	}
	else
	{

	}

	if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
	{
		//uiLookupCnt++;
		*puiLookupCntForDeleteList = uiLookupCnt;
	}


	//return NULL;
	return list_destination_n;	


}


destination_n* ProcessRoutingTableAccordingToRecentDeleteListV21(Node* node, UInt32 * puiRequireRediscovery, UInt32 * puiLookupCntForDeleteList)
{


	//now we just try a strict standard that only allow 

	destination_n * list_destination_n = NULL;



	RoutingOlsr * olsr = (RoutingOlsr *) node->appData.olsr;

	tco_node_addr * tco_delete_list_tmp = olsr->recent_delete_list;

	tco_node_addr * tco_delete_list_backup = NULL;

	while (tco_delete_list_tmp != NULL)
	{

		insert_into_tco_node_addr_set(&(tco_delete_list_backup), tco_delete_list_tmp->nid);

		tco_delete_list_tmp = tco_delete_list_tmp->next;
	}


	tco_delete_list_tmp = tco_delete_list_backup;

	UInt32 uiLookupCnt = 0;


	*puiRequireRediscovery = 0;
	//*pbRequireRediscovery = FALSE;


	//if (tco_delete_list_tmp->nid == 10 && olsr->naRecentChangedAddressByTC == 15 && node->nodeId == 16)
	//{

	//DebugBreak();
	//}


	//prte and prteTC will exist or non-exist at the same time
	rt_entry* prteTC = QueryRoutingTableAccordingToNodeId(node, olsr->naRecentChangedAddressByTC);
	if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
	{
		uiLookupCnt++;
	}

	if (prteTC != NULL)
	{

		
		//BOOL bEncounterCannotFindExchange = FALSE;

		BOOL bExistReachTCFromTDNodeTBD = FALSE;

		prteTC->rt_entry_infos.bDescendentRequireFurtherUpdate = FALSE;
		prteTC->rt_entry_infos.bCostChanged = FALSE;
		prteTC->rt_entry_infos.bRequireDelete = FALSE;

		prteTC->rt_entry_infos.uiCostChg = 0;


		while (tco_delete_list_tmp != NULL)
		{
			
			if (prteTC->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 == tco_delete_list_tmp->nid)
			{

				if (prteTC->rt_metric == 2)
				{

					BOOL b2HopNeighborCausedConnection = FALSE;
					b2HopNeighborCausedConnection = ConnectivetyCausedBy2HopNeighbor(node, prteTC->rt_entry_infos.rtu_dst, tco_delete_list_tmp->nid);

					if (b2HopNeighborCausedConnection)
					{

						remove_from_tco_node_addr_set(&(tco_delete_list_backup), tco_delete_list_tmp->nid);

						break;
					}										
				}
				


				bExistReachTCFromTDNodeTBD = TRUE;

				remove_from_tco_node_addr_set(&(tco_delete_list_backup), tco_delete_list_tmp->nid);


				break;
			}

			tco_delete_list_tmp = tco_delete_list_tmp->next;
		}


		if (bExistReachTCFromTDNodeTBD)
		{
			//DebugBreak();
			//the same as bExistReachTCFromTDNodeTBD for this specific case

			//find exchange for this,
			//if can not find, then do not do following further exchange
			BOOL bExchangeFound = FindRouteExchangeV21(node, NULL, prteTC, FALSE, NULL, &uiLookupCnt);

			if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
			{

				*puiLookupCntForDeleteList = uiLookupCnt;
			}

			if (!bExchangeFound)
			{

				//OlsrDeleteRoutingTable(prteTC);
				//prteTC = NULL;

				if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
				{
					//uiLookupCnt++;
					*puiLookupCntForDeleteList = uiLookupCnt;
				}


				if (tco_delete_list_backup != NULL)
				{
					clear_tco_node_addr_set(&tco_delete_list_backup);
				}

				//*pbRequireRediscovery = TRUE;
				*puiRequireRediscovery = 2;
				return NULL;
			}

		}
		else
		{

			
		}



		BOOL bEncounterCannotFindExchange = FALSE;



		tco_delete_list_tmp = tco_delete_list_backup;
		//now it should not including the entry get to TCNode, since it is removed from the list,
		//so only those nodes reached (it is possible that nodes can be reached but consider TCNode as last hop)
		//by TCNode is remained 


		tco_node_addr * disconnected_list = NULL;

		//int iDisconnectCount = 0;

		while (tco_delete_list_tmp != NULL)
		{

			rt_entry* prte = QueryRoutingTableAccordingToNodeId(node, tco_delete_list_tmp->nid);

			if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
			{
				uiLookupCnt++;
			}

			if (prte != NULL)
			{
				
				if (prte->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 == olsr->naRecentChangedAddressByTC)
				{

					if (prte->rt_metric == 2)
					{
						BOOL b2HopNeighborCausedConnection = FALSE;

						b2HopNeighborCausedConnection = ConnectivetyCausedBy2HopNeighbor(node, prte->rt_entry_infos.rtu_dst, olsr->naRecentChangedAddressByTC);
						if (b2HopNeighborCausedConnection)
						{

							

							tco_delete_list_tmp = tco_delete_list_tmp->next;

							continue;
						}
					}

					insert_into_tco_node_addr_set(&(disconnected_list), tco_delete_list_tmp->nid);
					//iDisconnectCount++;



				}
				else
				{
					//it is possible that nodes can be reached but not consider TCNode as last hop
					//skip these nodes

				}

			}
			else
			{

				//should not happen
			}


			tco_delete_list_tmp = tco_delete_list_tmp->next;
		}


		

		destination_n * list_destination_TS_plus_one = NULL;

		destination_n * list_destination_TS_plus_two = NULL;


		tco_node_addr * ATS_list = NULL;

		if (bExistReachTCFromTDNodeTBD && prteTC->rt_entry_infos.bDescendentRequireFurtherUpdate)
		{

			topology_last_entry * t_last_sym = OlsrLookupLastTopologyTableSYM(node, prteTC->rt_dst);
			
			if (t_last_sym != NULL)
			{
				if (prteTC->rt_entry_infos.bCostChanged)
				{
					//plus one
					destination_list* topo_dest = NULL;
					topo_dest = t_last_sym->topology_list_of_destinations;

					while (topo_dest != NULL)
					{

						Address addrReached = topo_dest->destination_node->topology_destination_dst;

						topo_dest = topo_dest->next;

						rt_entry* prteNearby = QueryRoutingTableAccordingToNodeId(node, addrReached.interfaceAddr.ipv4);

						if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
						{
							uiLookupCnt++;
						}

						if (prteNearby != NULL)
						{
							
							if (prteNearby->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 == olsr->naRecentChangedAddressByTC)
							{

								prteNearby->rt_entry_infos.bCostChanged = FALSE;
								prteNearby->rt_entry_infos.bDescendentRequireFurtherUpdate = FALSE;
								prteNearby->rt_entry_infos.bRequireDelete = FALSE;

								
								BOOL bExchangeFound = FindRouteExchangeV21(node, NULL, prteNearby, TRUE, prteTC, &uiLookupCnt);
								if (bExchangeFound)
								{

									if (prteNearby->rt_entry_infos.bDescendentRequireFurtherUpdate)
									{

										//add to list

										destination_n* list_destination_tmp;
										list_destination_tmp = (destination_n* )
											MEM_malloc(sizeof(destination_n));

										memset(
											list_destination_tmp,
											0,
											sizeof(destination_n));

										list_destination_tmp->destination = prteNearby;

										if (prteNearby->rt_entry_infos.bCostChanged)
										{

											//cost change, more specificly, plus one
											list_destination_tmp->next = list_destination_TS_plus_two;
											list_destination_TS_plus_two = list_destination_tmp;

										}
										else
										{
											//only route change
											list_destination_tmp->next = list_destination_TS_plus_one;
											list_destination_TS_plus_one = list_destination_tmp;
										}

									}
									else
									{
										//do not need to add to list, since all their descendants are not require change
									}
								}
								else
								{

									//will never happen, since at least the TC is ok,
								}

							}
						}
					}
					
					
				}
				else
				{
					//only route change
					destination_list* topo_dest = NULL;
					topo_dest = t_last_sym->topology_list_of_destinations;

					while (topo_dest != NULL)
					{

						Address addrReached = topo_dest->destination_node->topology_destination_dst;

						topo_dest = topo_dest->next;
						
						rt_entry* prteNearby = QueryRoutingTableAccordingToNodeId(node, addrReached.interfaceAddr.ipv4);

						if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
						{
							uiLookupCnt++;
						}

						if (prteNearby != NULL)
						{
							
							if (prteNearby->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 == olsr->naRecentChangedAddressByTC)
							{


								prteNearby->rt_entry_infos.uiCostChg = 0;

								prteNearby->rt_entry_infos.bCostChanged = FALSE;


								prteNearby->rt_entry_infos.bDescendentRequireFurtherUpdate = FALSE;
								prteNearby->rt_entry_infos.bRequireDelete = FALSE;

								//just change for same route
								BOOL bExchangeFound = FindRouteExchangeV20(node, NULL, prteNearby, TRUE, &uiLookupCnt);
								if (bExchangeFound)
								{

									if (prteNearby->rt_entry_infos.bDescendentRequireFurtherUpdate)
									{

										//add to list


										destination_n* list_destination_tmp;
										list_destination_tmp = (destination_n* )
											MEM_malloc(sizeof(destination_n));

										memset(
											list_destination_tmp,
											0,
											sizeof(destination_n));

										list_destination_tmp->destination = prteNearby;
										list_destination_tmp->next = list_destination_TS_plus_one;
										list_destination_TS_plus_one = list_destination_tmp;


									}						
								}
								else
								{

									//will never happen, since at least the TC is ok,
								}

							}
						}
					}
				}
			}			
		}
		else
		{
			//means ATS, if any, do not require further change, and so as their descendants

			//
		}


		//determine whether whether it is exchangeable for the DATS nodes
		
		//tco_node_addr * found_list = NULL;
		//tco_node_addr * possible_found_list = NULL;

		tco_node_addr * tmp_disconnected_list = NULL;


		if (disconnected_list != NULL)
		{
			

			while (disconnected_list != NULL)
			{
				
				//copy the set

				tco_node_addr * tmp_addr = disconnected_list;
				while (tmp_addr != NULL)
				{

					insert_into_tco_node_addr_set(&(tmp_disconnected_list), tmp_addr->nid);
					tmp_addr = tmp_addr->next;
				}

				tco_node_addr * tmp_addr_tmp = tmp_disconnected_list;

				BOOL bAtleastFindOne = FALSE;
				
				while (tmp_addr_tmp != NULL)
				{

					rt_entry* prte = QueryRoutingTableAccordingToNodeId(node, tmp_addr_tmp->nid);

					if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
					{
						uiLookupCnt++;
					}

					if (prte != NULL)
					{

						//the exchange here need to support unconsider set,
						//to avoid circular dependency 

						prte->rt_entry_infos.uiCostChg = 0;

						prte->rt_entry_infos.bCostChanged = FALSE;
						prte->rt_entry_infos.bDescendentRequireFurtherUpdate = FALSE;
						prte->rt_entry_infos.bRequireDelete = FALSE;


						BOOL bPToF = FALSE;
						BOOL bExchangeFound = FindRouteExchangeV21(node, NULL, prte, FALSE, NULL, &uiLookupCnt, FALSE, &(disconnected_list), NULL, NULL, NULL, NULL, &bPToF);

						if (!bExchangeFound)
						{

							if (bPToF)
							{
								//insert_into_tco_node_addr_set(&(possible_found_list), tmp_addr_tmp->nid);
								//DebugBreak();
							}
							else
							{

								//OlsrDeleteRoutingTable(prte);
								//prte = NULL;


								//*pbRequireRediscovery = TRUE;

								bEncounterCannotFindExchange = TRUE;

								break;
							}


						}
						else
						{
							remove_from_tco_node_addr_set(&(disconnected_list), tmp_addr_tmp->nid);
							//insert_into_tco_node_addr_set(&(found_list), tmp_addr_tmp->nid);

							bAtleastFindOne = TRUE;

							if (prte->rt_entry_infos.bDescendentRequireFurtherUpdate)
							{

								destination_n* list_destination_tmp;
								list_destination_tmp = (destination_n* )
									MEM_malloc(sizeof(destination_n));

								memset(
									list_destination_tmp,
									0,
									sizeof(destination_n));

								list_destination_tmp->destination = prte;

								if (prte->rt_entry_infos.bCostChanged)
								{
									
									//cost plus one
									list_destination_tmp->next = list_destination_TS_plus_two;
									list_destination_TS_plus_two = list_destination_tmp;
								}
								else
								{

									//only route change

									list_destination_tmp->next = list_destination_TS_plus_one;
									list_destination_TS_plus_one = list_destination_tmp;
								}								
								
							}
							else
							{
								//perfect exchange
							}

						}
					}

					tmp_addr_tmp = tmp_addr_tmp->next;
				}

				if (tmp_disconnected_list)
				{
					clear_tco_node_addr_set(&tmp_disconnected_list);
				}
			

				if (bEncounterCannotFindExchange)
				{
					break;
				}

				if (!bAtleastFindOne)
				{
					bEncounterCannotFindExchange = TRUE;
					break;
				}

			}



			
			
			
			if (bEncounterCannotFindExchange)
			{


				if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
				{
					//uiLookupCnt++;
					*puiLookupCntForDeleteList = uiLookupCnt;
				}

				//do Full Re-Calculation
				/*
				while (list_destination_n != NULL) 
				{

					destination_n* destination_n_1 = list_destination_n;
					list_destination_n = list_destination_n->next;
					MEM_free(destination_n_1);
				}
				*/

				while (list_destination_TS_plus_one != NULL)
				{
					destination_n* destination_n_1 = list_destination_TS_plus_one;
					list_destination_TS_plus_one = list_destination_TS_plus_one->next;
					MEM_free(destination_n_1);
				}

				list_destination_TS_plus_one = NULL;


				while (list_destination_TS_plus_two != NULL)
				{
					destination_n* destination_n_1 = list_destination_TS_plus_two;
					list_destination_TS_plus_two = list_destination_TS_plus_two->next;
					MEM_free(destination_n_1);
				}

				list_destination_TS_plus_two = NULL;

				if (disconnected_list != NULL)
				{
					clear_tco_node_addr_set(&disconnected_list);
				}


				//list_destination_n = NULL;

				if (tco_delete_list_backup != NULL)
				{
					clear_tco_node_addr_set(&tco_delete_list_backup);
				}

				//*pbRequireRediscovery = TRUE;
				*puiRequireRediscovery = 1;

				return NULL;

			}
			

			
		}
		else
		{
			//
		}


		//deal with list_destination_TS_plus_one list_destination_TS_plus_two

		if (list_destination_TS_plus_one != NULL || list_destination_TS_plus_two != NULL)
		{

			if (list_destination_TS_plus_one != NULL)
			{
				if (list_destination_TS_plus_two == NULL)
				{

				}
				else
				{
					// deal with list_destination_TS_plus_one
					// actually, only need to deal with route change here
 
					while (list_destination_TS_plus_one != NULL)
					{
						//DebugBreak();
						destination_n* destination_n_1 = NULL;
						destination_list* topo_dest = NULL;
						topology_last_entry* topo_last = OlsrLookupLastTopologyTableSYM(node, list_destination_TS_plus_one->destination->rt_dst);
						if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
						{
							uiLookupCnt++;
						}

						if (NULL != topo_last)
						{
							topo_dest = topo_last->topology_list_of_destinations;

							while (topo_dest != NULL)
							{

								Address addrReached = topo_dest->destination_node->topology_destination_dst;

								if (RoutingOlsrCheckMyIfaceAddress(
									node,
									topo_dest->destination_node->topology_destination_dst) != -1)
								{
									topo_dest = topo_dest->next;
									continue;
								}


								UInt32 uiInnerExchangeLUCnt = 0;


								//destination_n * list_destination_TS_plus_three = NULL;
								//here since only change for route, list_destination_TS_plus_three should not be needed

								OlsrCalculateRoutingTableForSinglePathTopologySearchHelpFuncV21(node, addrReached, list_destination_TS_plus_one, &list_destination_TS_plus_one, &list_destination_TS_plus_two, &uiInnerExchangeLUCnt);


								//Peter Added for test time complexity
								if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
								{
									uiLookupCnt += uiInnerExchangeLUCnt;

									//if (node->nodeId == NODE_ID_FOR_TEST_OUTER_ANGLE || node->nodeId == NODE_ID_FOR_TEST_OUTER_EDGE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_ANGLE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_EDGE || node->nodeId == NODE_ID_FOR_TEST_CENTER)
									if (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END)
									{
										uiLookupCnt++;

									}
								}

								topo_dest = topo_dest->next;
							}
						}

						destination_n_1 = list_destination_TS_plus_one;
						list_destination_TS_plus_one = list_destination_TS_plus_one->next;
						MEM_free(destination_n_1);
					}


				}
			}
			else
			{
				//only  list_destination_TS_plus_two
			}

		}
		else
		{
			//mean if any exchange exist, then all of them find perfect exchange, nothing required for further update, 
		}

		destination_n * list_destination_n_1 = list_destination_TS_plus_two;

		if (list_destination_n_1 != NULL)
		{

			//printf("OlsrCalculateRoutingTableAdv stage #2.2.1 \n");

				//printf("nodeId = %d \n", node->nodeId);
		

			//BOOL bFirstRound = TRUE;
			//do update WRT to lasthop for this case
			list_destination_n = list_destination_n_1;

			list_destination_n_1 = NULL;

			//destination_n* list_destination_n_2 = NULL;

			topology_last_entry* topo_last = NULL;
			destination_list* topo_dest = NULL;

			while (list_destination_n != NULL)
			{
				//list_destination_n_1 = NULL;

				//Peter comment: every loop add group of destination nodes that one hop more from the source node,
				//compare to the group in the previous loop  
				while (list_destination_n != NULL)
				{
					int iCosttmp = -1;
					
					destination_n* destination_n_1 = NULL;

					if (DEBUG)
					{
						char addrString[MAX_STRING_LENGTH];

						IO_ConvertIpAddressToString(
							&list_destination_n->destination->rt_dst,
							addrString);

						printf("Node %d, Last hop %s\n",
							node->nodeId,
							addrString);
					}

					//Peter comment: find from the topology table if there is some entry 
					//whose last hop equal the specific dest hop of 2 or more (* since every loop will
					// increase the one more hop count) hop neighbors
					if (SYMMETRIC_TOPOLOGY_TABLE)
					{
						topo_last = OlsrLookupLastTopologyTableSYM(node, list_destination_n->destination->rt_dst);
					}
					else
					{
						topo_last = OlsrLookupLastTopologyTable(node, list_destination_n->destination->rt_dst);
					}


					if (NULL != topo_last)
					{
						topo_dest = topo_last->topology_list_of_destinations;

						while (topo_dest != NULL)
						{

							Address addrReached = topo_dest->destination_node->topology_destination_dst;

							if (RoutingOlsrCheckMyIfaceAddress(
								node,
								topo_dest->destination_node->topology_destination_dst) != -1)
							{
								topo_dest = topo_dest->next;
								continue;
							}


							UInt32 uiInnerExchangeLUCnt = 0;
							OlsrCalculateRoutingTableForSinglePathTopologySearchHelpFuncV21(node, addrReached, list_destination_n, &list_destination_n, &list_destination_n_1, &uiInnerExchangeLUCnt);


							//Peter Added for test time complexity
							if (_TEST_TIME_COMPLEXITY)
							{
								uiLookupCnt += uiInnerExchangeLUCnt;

								//if (node->nodeId == NODE_ID_FOR_TEST_OUTER_ANGLE || node->nodeId == NODE_ID_FOR_TEST_OUTER_EDGE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_ANGLE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_EDGE || node->nodeId == NODE_ID_FOR_TEST_CENTER)
								if (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END)
								{
									uiLookupCnt++;

								}
							}

							topo_dest = topo_dest->next;
						}
					}

					destination_n_1 = list_destination_n;
					list_destination_n = list_destination_n->next;

					/*
					if (iCosttmp == -1)
					{
						iCosttmp = destination_n_1->destination->rt_entry_infos.rtu_metric;

					}
					else
					{
						if (iCosttmp == destination_n_1->destination->rt_entry_infos.rtu_metric)
						{

						}
						else
						{
							printf("******************************&&&&&&&&&&&& cost mismatch!!!  iCosttmp = %d while destination_n_1->destination->rt_entry_infos.rtu_metric = %d \n", 
								iCosttmp, destination_n_1->destination->rt_entry_infos.rtu_metric);
						}
					}

					//printf("******************************&&&&&&&&&&&&  nodeId= %d, iCosttmp = %d \n", node->nodeId, iCosttmp);
					*/

					MEM_free(destination_n_1);
				}

				/*
				list_destination_n = list_destination_n_1;
				
				*/

				if (list_destination_n_1 != NULL)
				{
					list_destination_n = list_destination_n_1;
					
					//list_destination_n_1 = list_destination_n_2;
					list_destination_n_1 = NULL;
					//list_destination_n_2 = NULL;
				}
				else
				{
											
					list_destination_n = NULL;
					
					/*
					if (list_destination_n_2 != NULL)
					{
						list_destination_n = list_destination_n_2;
						
						//list_destination_n_1 is already NULL
						list_destination_n_2 = NULL;
					}
					else
					{
						//no new entry require to be further update, so end here
						list_destination_n = NULL;
						//list_destination_n_1 is already NULL
						//list_destination_n_2 is already NULL
						//break;
					}
					*/
				}

				//ui_metric_cost_limitation++;

				//bFirstRound = FALSE;
			}

			//printf("OlsrCalculateRoutingTableAdv stage #2.2.2 \n");

		
		}
		
						
		if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
		{
			//uiLookupCnt++;
			*puiLookupCntForDeleteList = uiLookupCnt;
		}


	}
	else
	{
		//process for delete is not required 
	}

	if (tco_delete_list_backup != NULL)
	{
		clear_tco_node_addr_set(&tco_delete_list_backup);
	}

	//return NULL;
	return list_destination_n;	

}






destination_n* ProcessRoutingTableAccordingToRecentDeleteListV20(Node* node, BOOL * pbRequireRediscovery, UInt32 * puiLookupCntForDeleteList)
{


	//now we just try a strict standard that only allow 

	destination_n * list_destination_n_1 = NULL;

	RoutingOlsr * olsr = (RoutingOlsr *) node->appData.olsr;

	tco_node_addr * tco_delete_list_tmp = olsr->recent_delete_list;			

	UInt32 uiLookupCnt = 0;

	*pbRequireRediscovery = FALSE;


	//if (tco_delete_list_tmp->nid == 10 && olsr->naRecentChangedAddressByTC == 15 && node->nodeId == 16)
	//{

		//DebugBreak();
	//}


	//prte and prteTC will exist or non-exist at the same time
	rt_entry* prteTC = QueryRoutingTableAccordingToNodeId(node, olsr->naRecentChangedAddressByTC);
	if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
	{
		uiLookupCnt++;
	}

	if (prteTC != NULL)
	{


		//BOOL bEncounterCannotFindExchange = FALSE;

		BOOL bExistReachTCFromTDNodeTBD = FALSE;

		prteTC->rt_entry_infos.bDescendentRequireFurtherUpdate = FALSE;
		prteTC->rt_entry_infos.bCostChanged = FALSE;
		prteTC->rt_entry_infos.bRequireDelete = FALSE;

		prteTC->rt_entry_infos.uiCostChg = 0;


		while (tco_delete_list_tmp != NULL)
		{

			if (prteTC->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 == tco_delete_list_tmp->nid)
			{

				if (prteTC->rt_metric == 2)
				{

					BOOL b2HopNeighborCausedConnection = FALSE;
					b2HopNeighborCausedConnection = ConnectivetyCausedBy2HopNeighbor(node, prteTC->rt_entry_infos.rtu_dst, tco_delete_list_tmp->nid);

					if (b2HopNeighborCausedConnection)
					{

						remove_from_tco_node_addr_set(&(olsr->recent_delete_list), tco_delete_list_tmp->nid);

						break;
					}										
				}



				bExistReachTCFromTDNodeTBD = TRUE;

				remove_from_tco_node_addr_set(&(olsr->recent_delete_list), tco_delete_list_tmp->nid);


				break;
			}

			tco_delete_list_tmp = tco_delete_list_tmp->next;
		}


		if (bExistReachTCFromTDNodeTBD)
		{

			//the same as bExistReachTCFromTDNodeTBD for this specific case

			//find exchange for this,
			//if can not find, then do not do following further exchange
			BOOL bExchangeFound = FindRouteExchangeV20(node, NULL, prteTC, FALSE, &uiLookupCnt);

			if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
			{

				*puiLookupCntForDeleteList = uiLookupCnt;
			}

			if (!bExchangeFound)
			{

				//OlsrDeleteRoutingTable(prteTC);
				//prteTC = NULL;

				if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
				{
					//uiLookupCnt++;
					*puiLookupCntForDeleteList = uiLookupCnt;
				}

				*pbRequireRediscovery = TRUE;
				return NULL;
			}

		}
		else
		{

			//further check for bRequireUpdate is not needed for this specific case
		}



		//µ½Õâ²½£¬¾ÍËµÃ÷ bExistReachTCFromTDNodeTBD ²»»áÔì³ÉÈÎºÎ cost µÄ¸Ä±ä
		//FindRouteExchangeV20 Ö»ÔÊÐí×î¶àÊÇroute ±ä»¯
	
		BOOL bEncounterCannotFindExchange = FALSE;

		

		tco_delete_list_tmp = olsr->recent_delete_list;
		//now it should not including the entry get to TCNode, since it is removed from the list,
		//so only those nodes reached (it is possible that nodes can be reached but consider TCNode as last hop)
		//by TCNode is remained 

		//tco_node_addr * disconnected_list = NULL;

		//int iDisconnectCount = 0;
		
		while (tco_delete_list_tmp != NULL)
		{

			rt_entry* prte = QueryRoutingTableAccordingToNodeId(node, tco_delete_list_tmp->nid);

			if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
			{
				uiLookupCnt++;
			}

			if (prte != NULL)
			{

				

				if (prte->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 == olsr->naRecentChangedAddressByTC)
				{

					if (prte->rt_metric == 2)
					{
						BOOL b2HopNeighborCausedConnection = FALSE;

						b2HopNeighborCausedConnection = ConnectivetyCausedBy2HopNeighbor(node, prte->rt_entry_infos.rtu_dst, olsr->naRecentChangedAddressByTC);
						if (b2HopNeighborCausedConnection)
						{

							//remove_from_tco_node_addr_set(&(olsr->recent_delete_list), tco_delete_list_tmp->nid);

							tco_delete_list_tmp = tco_delete_list_tmp->next;

							continue;
						}
					}
					
					//insert_into_tco_node_addr_set(&(disconnected_list), tco_delete_list_tmp->nid);
					//iDisconnectCount++;


					//prte->rt_entry_infos.bRequireExchange = TRUE;
					//prte->rt_entry_infos.bRequireUpdate = FALSE;	


					prte->rt_entry_infos.uiCostChg = 0;

					prte->rt_entry_infos.bCostChanged = FALSE;
					prte->rt_entry_infos.bDescendentRequireFurtherUpdate = FALSE;
					

					BOOL bExchangeFound = FindRouteExchangeV20(node, NULL, prte, FALSE, &uiLookupCnt);
					if (!bExchangeFound)
					{

						//OlsrDeleteRoutingTable(prte);
						//prte = NULL;

						*pbRequireRediscovery = TRUE;

						bEncounterCannotFindExchange = TRUE;

						break;
					}
					else
					{

						if (prte->rt_entry_infos.bDescendentRequireFurtherUpdate)
						{

							destination_n* list_destination_tmp;
							list_destination_tmp = (destination_n* )
								MEM_malloc(sizeof(destination_n));

							memset(
								list_destination_tmp,
								0,
								sizeof(destination_n));

							list_destination_tmp->destination = prte;
							list_destination_tmp->next = list_destination_n_1;
							list_destination_n_1 = list_destination_tmp;
						}
						
					}					
				
				}
				else
				{
					//it is possible that nodes can be reached but not consider TCNode as last hop
					//skip these nodes

				}

			}
			else
			{

				//should not happen
			}


			tco_delete_list_tmp = tco_delete_list_tmp->next;
		}


		if (bEncounterCannotFindExchange)
		{


			if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
			{
				//uiLookupCnt++;
				*puiLookupCntForDeleteList = uiLookupCnt;
			}

			//do Full Re-Calculation
			while (list_destination_n_1 != NULL) 
			{

				destination_n* destination_n_1 = list_destination_n_1;
				list_destination_n_1 = list_destination_n_1->next;
				MEM_free(destination_n_1);
			}

			list_destination_n_1 = NULL;

			*pbRequireRediscovery = TRUE;

			return NULL;

		}
		



		topology_last_entry * t_last_sym = OlsrLookupLastTopologyTableSYM(node, prteTC->rt_dst);
		if (t_last_sym != NULL && bExistReachTCFromTDNodeTBD && prteTC->rt_entry_infos.bDescendentRequireFurtherUpdate)
		{

			destination_list* topo_dest = NULL;
			topo_dest = t_last_sym->topology_list_of_destinations;


			while (topo_dest != NULL)
			{

				Address addrReached = topo_dest->destination_node->topology_destination_dst;


				topo_dest = topo_dest->next;

				rt_entry* prteNearby = QueryRoutingTableAccordingToNodeId(node, addrReached.interfaceAddr.ipv4);

				if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
				{
					uiLookupCnt++;
				}

				if (prteNearby != NULL)
				{
					

					if (prteNearby->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 == olsr->naRecentChangedAddressByTC)
					{

						prteNearby->rt_entry_infos.uiCostChg = 0;

						prteNearby->rt_entry_infos.bCostChanged = FALSE;
						prteNearby->rt_entry_infos.bDescendentRequireFurtherUpdate = FALSE;
						prteNearby->rt_entry_infos.bRequireDelete = FALSE;

						//just change for same route
						BOOL bExchangeFound = FindRouteExchangeV20(node, NULL, prteNearby, TRUE, &uiLookupCnt);
						if (bExchangeFound)
						{
						
							if (prteNearby->rt_entry_infos.bDescendentRequireFurtherUpdate)
							{

								//add to list


								destination_n* list_destination_tmp;
								list_destination_tmp = (destination_n* )
									MEM_malloc(sizeof(destination_n));

								memset(
									list_destination_tmp,
									0,
									sizeof(destination_n));

								list_destination_tmp->destination = prteNearby;
								list_destination_tmp->next = list_destination_n_1;
								list_destination_n_1 = list_destination_tmp;

							
							}						
						}
						else
						{

							//will not happen
						}
					

					}
				
				}

			}

		}
		




		if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
		{
			//uiLookupCnt++;
			*puiLookupCntForDeleteList = uiLookupCnt;
		}

		if (bEncounterCannotFindExchange)
		{

			//do Full Re-Calculation
			while (list_destination_n_1 != NULL) 
			{

				destination_n* destination_n_1 = list_destination_n_1;
				list_destination_n_1 = list_destination_n_1->next;
				MEM_free(destination_n_1);
			}

			list_destination_n_1 = NULL;

			*pbRequireRediscovery = TRUE;

			return NULL;

		}


		//should success, further process the update list:
		if (list_destination_n_1 != NULL)
		{

			//printf("OlsrCalculateRoutingTableAdv stage #2.2.1 \n");

			//printf("nodeId = %d \n", node->nodeId);


			//BOOL bFirstRound = TRUE;
			//do update WRT to lasthop for this case
			destination_n * list_destination_n = list_destination_n_1;

			while (list_destination_n_1 != NULL)
			{
				list_destination_n_1 = NULL;

				topology_last_entry* topo_last = NULL;
				destination_list* topo_dest = NULL;


				//Peter comment: every loop add group of destination nodes that one hop more from the source node,
				//compare to the group in the previous loop  
				while (list_destination_n != NULL)
				{
					destination_n* destination_n_1 = NULL;

					if (DEBUG)
					{
						char addrString[MAX_STRING_LENGTH];

						IO_ConvertIpAddressToString(
							&list_destination_n->destination->rt_dst,
							addrString);

						printf("Node %d, Last hop %s\n",
							node->nodeId,
							addrString);
					}

					//Peter comment: find from the topology table if there is some entry 
					//whose last hop equal the specific dest hop of 2 or more (* since every loop will
					// increase the one more hop count) hop neighbors
					if (SYMMETRIC_TOPOLOGY_TABLE)
					{
						topo_last = OlsrLookupLastTopologyTableSYM(node, list_destination_n->destination->rt_dst);
					}
					else
					{
						topo_last = OlsrLookupLastTopologyTable(node, list_destination_n->destination->rt_dst);
					}


					if (NULL != topo_last)
					{
						topo_dest = topo_last->topology_list_of_destinations;

						while (topo_dest != NULL)
						{

							Address addrReached = topo_dest->destination_node->topology_destination_dst;

							if (RoutingOlsrCheckMyIfaceAddress(
								node,
								topo_dest->destination_node->topology_destination_dst) != -1)
							{
								topo_dest = topo_dest->next;
								continue;
							}


							UInt32 uiInnerExchangeLUCnt = 0;
							OlsrCalculateRoutingTableForSinglePathTopologySearchHelpFuncV20(node, addrReached, list_destination_n, &list_destination_n_1, &uiInnerExchangeLUCnt);


							//Peter Added for test time complexity
							if (_TEST_TIME_COMPLEXITY)
							{
								uiLookupCnt += uiInnerExchangeLUCnt;

								//if (node->nodeId == NODE_ID_FOR_TEST_OUTER_ANGLE || node->nodeId == NODE_ID_FOR_TEST_OUTER_EDGE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_ANGLE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_EDGE || node->nodeId == NODE_ID_FOR_TEST_CENTER)
								if (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END)
								{
									uiLookupCnt++;

								}
							}

							topo_dest = topo_dest->next;
						}
					}

					destination_n_1 = list_destination_n;
					list_destination_n = list_destination_n->next;
					MEM_free(destination_n_1);
				}

				list_destination_n = list_destination_n_1;
				//ui_metric_cost_limitation++;

				//bFirstRound = FALSE;
			}


			//printf("OlsrCalculateRoutingTableAdv stage #2.2.2 \n");
		}

	}
	else
	{
		//process for delete is not required 
	}



	return list_destination_n_1;	

}

destination_n* ProcessRoutingTableAccordingToRecentDeleteListV3(Node* node, BOOL * pbRequireRediscovery, UInt32 * puiLookupCntForDeleteList)
{

	destination_n * list_destination_n = NULL;

	RoutingOlsr * olsr = (RoutingOlsr *) node->appData.olsr;

	tco_node_addr * tco_delete_list_tmp = olsr->recent_delete_list;			

	UInt32 uiLookupCnt = 0;

	*pbRequireRediscovery = FALSE;

	
	//if (tco_delete_list_tmp->nid == 10 && olsr->naRecentChangedAddressByTC == 15 && node->nodeId == 16)
	{

		//DebugBreak();
	}
	
	
	BOOL bCannotFindExchangeForAtLeastOneDest = FALSE;
	

	//prte and prteTC will exist or non-exist at the same time
	rt_entry* prteTC = QueryRoutingTableAccordingToNodeId(node, olsr->naRecentChangedAddressByTC);
	if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
	{
		uiLookupCnt++;
	}

	if (prteTC != NULL)
	{

		BOOL bExistReachTCFromTDNodeTBD = FALSE;

		prteTC->rt_entry_infos.bDescendentRequireFurtherUpdate = FALSE;
		prteTC->rt_entry_infos.bCostChanged = FALSE;
		prteTC->rt_entry_infos.bRequireDelete = FALSE;

		prteTC->rt_entry_infos.uiCostChg = 0;


		while (tco_delete_list_tmp != NULL)
		{
			
			if (prteTC->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 == tco_delete_list_tmp->nid)
			{

				if (prteTC->rt_metric == 2)
				{

					BOOL b2HopNeighborCausedConnection = FALSE;
					b2HopNeighborCausedConnection = ConnectivetyCausedBy2HopNeighbor(node, prteTC->rt_entry_infos.rtu_dst, tco_delete_list_tmp->nid);

					if (b2HopNeighborCausedConnection)
					{

						remove_from_tco_node_addr_set(&(olsr->recent_delete_list), tco_delete_list_tmp->nid);

						break;
					}										
				}
				


				bExistReachTCFromTDNodeTBD = TRUE;

				remove_from_tco_node_addr_set(&(olsr->recent_delete_list), tco_delete_list_tmp->nid);


				break;
			}

			tco_delete_list_tmp = tco_delete_list_tmp->next;
		}


		if (bExistReachTCFromTDNodeTBD)
		{

			//the same as bExistReachTCFromTDNodeTBD for this specific case

			//find exchange for this,
			//if can not find, then do not do following further exchange
			BOOL bExchangeFound = FindRouteExchangeV2(node, prteTC, FALSE, &uiLookupCnt);

			if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
			{
				
				*puiLookupCntForDeleteList = uiLookupCnt;
			}

			if (!bExchangeFound)
			{

				//OlsrDeleteRoutingTable(prteTC);
				//prteTC = NULL;
			
				*pbRequireRediscovery = TRUE;
				return NULL;
			}
			
		}
		else
		{

			//further check for bRequireUpdate is not needed for this specific case
		}


	

		BOOL bEncounterCannotFindExchange = FALSE;

		

		tco_delete_list_tmp = olsr->recent_delete_list;
		//now it should not including the entry get to TCNode, since it is removed from the list,
		//so only those nodes reached (it is possible that nodes can be reached but consider TCNode as last hop)
		//by TCNode is remained 

		tco_node_addr * disconnected_list = NULL;
		
		while (tco_delete_list_tmp != NULL)
		{

			rt_entry* prte = QueryRoutingTableAccordingToNodeId(node, tco_delete_list_tmp->nid);

			if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
			{
				uiLookupCnt++;
			}

			if (prte != NULL)
			{

				//prte->rt_entry_infos.bRequireExchange = FALSE;
				//prte->rt_entry_infos.bRequireUpdate = FALSE;

				prte->rt_entry_infos.uiCostChg = 0;

				prte->rt_entry_infos.bCostChanged = FALSE;
				prte->rt_entry_infos.bDescendentRequireFurtherUpdate = FALSE;
				prteTC->rt_entry_infos.bRequireDelete = FALSE;

				if (prte->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 == olsr->naRecentChangedAddressByTC)
				{

					if (prte->rt_metric == 2)
					{
						BOOL b2HopNeighborCausedConnection = FALSE;

						b2HopNeighborCausedConnection = ConnectivetyCausedBy2HopNeighbor(node, prte->rt_entry_infos.rtu_dst, olsr->naRecentChangedAddressByTC);
						if (b2HopNeighborCausedConnection)
						{

							//remove_from_tco_node_addr_set(&(olsr->recent_delete_list), tco_delete_list_tmp->nid);

							tco_delete_list_tmp = tco_delete_list_tmp->next;

							continue;
						}
					}
					
					insert_into_tco_node_addr_set(&(disconnected_list), tco_delete_list_tmp->nid);


					//prte->rt_entry_infos.bRequireExchange = TRUE;
					//prte->rt_entry_infos.bRequireUpdate = FALSE;					
					
				
				}
				else
				{
					//it is possible that nodes can be reached but not consider TCNode as last hop
					//skip these nodes

				}

			}
			else
			{

				//should not happen
			}


			tco_delete_list_tmp = tco_delete_list_tmp->next;
		}



		//!!!!!¼´Ê¹ÓÃÕâÖÖ°ì·¨Ò²ÎÞ·¨±ÜÃâ¼ä½ÓµÄ»¥ÏàÒÀÀµ
		//Even if use this method, indirect dependency is still hard to avoid

		//Try the first round, do not consider nodes in disconnected_list as potential exchanger at this time.
		tco_node_addr * found_list = NULL;
		tco_node_addr * possible_found_list = NULL;


		tco_node_addr * tmp_disconnected_list = disconnected_list;
		while (tmp_disconnected_list != NULL)
		{

			rt_entry* prte = QueryRoutingTableAccordingToNodeId(node, tmp_disconnected_list->nid);

			if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
			{
				uiLookupCnt++;
			}

			if (prte != NULL)
			{
			
				//the exchange here need to support unconsider set,
				//to avoid circular dependency 

				BOOL bPToF = FALSE;
				BOOL bExchangeFound = FindRouteExchangeV2(node, prte, FALSE, &uiLookupCnt, FALSE, &(disconnected_list), &bPToF);

				if (!bExchangeFound)
				{

					
					if (!bPToF)
					{
						insert_into_tco_node_addr_set(&(possible_found_list), tmp_disconnected_list->nid);
					}
					else
					{

						//OlsrDeleteRoutingTable(prte);
						//prte = NULL;


						*pbRequireRediscovery = TRUE;

						bEncounterCannotFindExchange = TRUE;

						break;
					}

					
				}
				else
				{

					insert_into_tco_node_addr_set(&(found_list), tmp_disconnected_list->nid);

					//if (prte->rt_entry_infos.bDescendentRequireFurtherUpdate)
					{
						
						destination_n* list_destination_tmp;
						list_destination_tmp = (destination_n* )
							MEM_malloc(sizeof(destination_n));

						memset(
							list_destination_tmp,
							0,
							sizeof(destination_n));

						list_destination_tmp->destination = prte;
						list_destination_tmp->next = list_destination_n;
						list_destination_n = list_destination_tmp;
					}
					
				}
			}

			tmp_disconnected_list = tmp_disconnected_list->next;
		}


		


		if (bEncounterCannotFindExchange || !bEncounterCannotFindExchange && possible_found_list != NULL && found_list == NULL)
		{

			//some node can not find exchange, or all the unfound are mutual dependent, without any furthur oppotunity in found_list

			//clear the lists

			if (disconnected_list)
			{

				clear_tco_node_addr_set(&disconnected_list);
			}

			if (found_list)
			{
				clear_tco_node_addr_set(&found_list);
			}
			
			if (possible_found_list)
			{
				clear_tco_node_addr_set(&possible_found_list);
			}
			

			//do Full Re-Calculation
			while (list_destination_n != NULL) 
			{

				destination_n* destination_n_1 = list_destination_n;
				list_destination_n = list_destination_n->next;
				MEM_free(destination_n_1);
			}

			list_destination_n = NULL;

			*pbRequireRediscovery = TRUE;

		
			if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
			{
				//uiLookupCnt++;
				*puiLookupCntForDeleteList = uiLookupCnt;
			}
			
			return NULL;

		}
		else //!bEncounterCannotFindExchange && 
		{
			//the second round of exchange, 
			//only use the found_list for exchange

			if (possible_found_list != NULL)
			{
				while (possible_found_list != NULL)
				{
					//must be found_list != NULL 

					tco_node_addr * tmp_possible_found_list = NULL;
					tco_node_addr * tmp_addr = possible_found_list;

					//copy current possible list
					while (tmp_addr != NULL)
					{

						insert_into_tco_node_addr_set(&(tmp_possible_found_list), tmp_addr->nid);

						tmp_addr = tmp_addr->next;
					}

					tco_node_addr * tmp_possible_addr = tmp_possible_found_list;

					BOOL bUpdated = FALSE;

					while (tmp_possible_addr != NULL)
					{

						rt_entry* prte = QueryRoutingTableAccordingToNodeId(node, tmp_possible_addr->nid);

						if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
						{
							uiLookupCnt++;
						}

						if (prte != NULL)
						{


							if (FindLastExchange(node, prte, &found_list, &uiLookupCnt))
							{

								insert_into_tco_node_addr_set(&(found_list), tmp_possible_addr->nid);

								remove_from_tco_node_addr_set(&possible_found_list, tmp_possible_addr->nid);

									bUpdated = TRUE;
								//break;
							}

						}


						tmp_possible_addr = tmp_possible_addr->next;
					}

					if (tmp_possible_found_list != NULL)
					{

						clear_tco_node_addr_set(&tmp_possible_found_list);
					}

					if (!bUpdated)
					{
						//so there would be some possible route can never found reasonable exchange,

						if (disconnected_list)
						{

							clear_tco_node_addr_set(&disconnected_list);
						}

						if (found_list)
						{
							clear_tco_node_addr_set(&found_list);
						}

						if (possible_found_list)
						{
							clear_tco_node_addr_set(&possible_found_list);
						}

						//do Full Re-Calculation
						while (list_destination_n != NULL) 
						{

							destination_n* destination_n_1 = list_destination_n;
							list_destination_n = list_destination_n->next;
							MEM_free(destination_n_1);
						}

						list_destination_n = NULL;

						*pbRequireRediscovery = TRUE;


						if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
						{
							//uiLookupCnt++;
							*puiLookupCntForDeleteList = uiLookupCnt;
						}

						return NULL;

						//break;
					}								
				}


			}
			else
			{
				//all are already in found_list and in output list

				//It is possible that further update is not needed.
				
			}
						
			//all are in found_list and in output list now 		
			
		}


		topology_last_entry * t_last_sym = OlsrLookupLastTopologyTableSYM(node, prteTC->rt_dst);
		if (t_last_sym != NULL && bExistReachTCFromTDNodeTBD)
		{

			destination_list* topo_dest = NULL;
			topo_dest = t_last_sym->topology_list_of_destinations;




			//rt_entry* prtetmpFormer = NULL;

			//BOOL bSameCostFormer = FALSE;
			//BOOL bCostPlusOneFormer = FALSE;

			//BOOL bExistSameCostWithSameRouterFormer = FALSE;

			while (topo_dest != NULL)
			{

				Address addrReached = topo_dest->destination_node->topology_destination_dst;


				topo_dest = topo_dest->next;

				rt_entry* prteNearby = QueryRoutingTableAccordingToNodeId(node, addrReached.interfaceAddr.ipv4);

				if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
				{
					uiLookupCnt++;
				}

				if (prteNearby != NULL)
				{


					//prteNearby->rt_entry_infos.bRequireExchange = FALSE;
					//prteNearby->rt_entry_infos.bRequireUpdate = FALSE;
					prteNearby->rt_entry_infos.bCostChanged = FALSE;
					prteNearby->rt_entry_infos.bDescendentRequireFurtherUpdate = FALSE;
					prteNearby->rt_entry_infos.bRequireDelete = FALSE;


					prteNearby->rt_entry_infos.uiCostChg = 0;



					if (prteNearby->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 == olsr->naRecentChangedAddressByTC)
					{

						//if (bExistReachTCFromTDNodeTBD)
						{

							if (prteTC->rt_entry_infos.bDescendentRequireFurtherUpdate)
							{

								if (prteTC->rt_entry_infos.bCostChanged)
								{

									//prteNearby->rt_entry_infos.bRequireExchange = TRUE;


									//prteNearby->rt_entry_infos.bRequireUpdate = FALSE;



									BOOL bExchangeFound = FindRouteExchangeV2(node, prteNearby, TRUE, &uiLookupCnt);

									if (!bExchangeFound)
									{

										OlsrDeleteRoutingTable(prteNearby);
										prteNearby = NULL;

										*pbRequireRediscovery = TRUE;

										bEncounterCannotFindExchange = TRUE;

										break;
									}

								}
								else
								{
									//only route changed  

									//prteNearby->rt_entry_infos.bRequireExchange = FALSE;

									//prteNearby->rt_entry_infos.bRequireUpdate = TRUE;

									prteNearby->rt_interface = prteTC->rt_interface;
									prteNearby->rt_router = prteTC->rt_router;

									if (_OLSR_MULTIPATH)
									{


										prteNearby->rt_entry_infos.rtu_DegreeWRTNode = prteTC->rt_entry_infos.rtu_DegreeWRTNode;
										prteNearby->rt_entry_infos.rtu_DistanceWRTNode = prteTC->rt_entry_infos.rtu_DistanceWRTNode;
										prteNearby->rt_entry_infos.related_neighbor = prteTC->rt_entry_infos.related_neighbor;
									}

									prteNearby->rt_entry_infos.bDescendentRequireFurtherUpdate = TRUE;
									prteNearby->rt_entry_infos.bCostChanged = FALSE;
									prteNearby->rt_entry_infos.bRequireDelete = FALSE;

									prteNearby->rt_entry_infos.uiCostChg = 0;

								}
							}
						
						
							//add to list


							destination_n* list_destination_tmp;
							list_destination_tmp = (destination_n* )
								MEM_malloc(sizeof(destination_n));

							memset(
								list_destination_tmp,
								0,
								sizeof(destination_n));

							list_destination_tmp->destination = prteNearby;
							list_destination_tmp->next = list_destination_n;
							list_destination_n = list_destination_tmp;

						}
						/*
						else
						{

							//mean these nodes do not need to update wrt to the earlier exchange (the node that can reach TCNode) happened,
							//but just need to consider themselves

							

						}
						*/

					}

				

				
				}

			}


		}


		if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
		{
			//uiLookupCnt++;
			*puiLookupCntForDeleteList = uiLookupCnt;
		}

		if (bEncounterCannotFindExchange)
		{

			//do Full Re-Calculation
			while (list_destination_n != NULL) 
			{

				destination_n* destination_n_1 = list_destination_n;
				list_destination_n = list_destination_n->next;
				MEM_free(destination_n_1);
			}

			list_destination_n = NULL;

			*pbRequireRediscovery = TRUE;

			return NULL;

		}

	}
	else
	{
		//process for delete is not required 
	}


	
	return list_destination_n;
}



destination_n* ProcessRoutingTableAccordingToRecentDeleteListV2(Node* node, BOOL * pbRequireRediscovery, UInt32 * puiLookupCntForDeleteList)
{

	destination_n * list_destination_n = NULL;

	RoutingOlsr * olsr = (RoutingOlsr *) node->appData.olsr;

	tco_node_addr * tco_delete_list_tmp = olsr->recent_delete_list;			

	UInt32 uiLookupCnt = 0;

	*pbRequireRediscovery = FALSE;

	
	//if (tco_delete_list_tmp->nid == 10 && olsr->naRecentChangedAddressByTC == 15 && node->nodeId == 16)
	{

		//DebugBreak();
	}
	
	
	BOOL bCannotFindExchangeForAtLeastOneDest = FALSE;
	

	//prte and prteTC will exist or non-exist at the same time
	rt_entry* prteTC = QueryRoutingTableAccordingToNodeId(node, olsr->naRecentChangedAddressByTC);


	if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
	{
		uiLookupCnt++;
	}

	if (prteTC != NULL)
	{

		BOOL bExistReachTCFromTDNodeTBD = FALSE;

		//prteTC->rt_entry_infos.bRequireUpdate = FALSE;
		//prteTC->rt_entry_infos.bRequireExchange = FALSE;
		prteTC->rt_entry_infos.bDescendentRequireFurtherUpdate = FALSE;
		prteTC->rt_entry_infos.bCostChanged = FALSE;
		prteTC->rt_entry_infos.bRequireDelete = FALSE;

		prteTC->rt_entry_infos.uiCostChg = 0;


		while (tco_delete_list_tmp != NULL)
		{
			
			if (prteTC->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 == tco_delete_list_tmp->nid)
			{

				//OlsrLookup2HopNeighborTable
				if (prteTC->rt_metric == 2)
				{

					neighbor_2_entry *two_hop_neighbor = NULL;

					two_hop_neighbor = OlsrLookup2HopNeighborTable(node, prteTC->rt_entry_infos.rtu_dst);

					if (two_hop_neighbor)
					{
						neighbor_list_entry* list_1 = NULL;

						list_1 = two_hop_neighbor->neighbor_2_nblist;

						BOOL b2HopNeighborCausedConnection = FALSE;
						while (list_1 != NULL)
						{
							if (list_1->neighbor->neighbor_main_addr.interfaceAddr.ipv4 == tco_delete_list_tmp->nid)
							{
								b2HopNeighborCausedConnection = TRUE;
								break;
							}

							list_1 = list_1->neighbor_next;
						}

						if (b2HopNeighborCausedConnection)
						{


							remove_from_tco_node_addr_set(&(olsr->recent_delete_list), tco_delete_list_tmp->nid);

							break;
						}
					}
				}
				


				bExistReachTCFromTDNodeTBD = TRUE;

				remove_from_tco_node_addr_set(&(olsr->recent_delete_list), tco_delete_list_tmp->nid);


				//prteTC->rt_entry_infos.bRequireUpdate = FALSE;
				
				//prteTC->rt_entry_infos.bRequireExchange = TRUE;

				

				break;
			}

			tco_delete_list_tmp = tco_delete_list_tmp->next;
		}


		if (bExistReachTCFromTDNodeTBD)
		//if (prteTC->rt_entry_infos.bRequireExchange)
		{

			//the same as bExistReachTCFromTDNodeTBD for this specific case

			//find exchange for this,
			//if can not find, then do not do following further exchange
			BOOL bExchangeFound = FindRouteExchange(node, prteTC, FALSE, &uiLookupCnt);

			if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
			{
				
				*puiLookupCntForDeleteList = uiLookupCnt;
			}

			if (!bExchangeFound)
			{

				OlsrDeleteRoutingTable(prteTC);
				prteTC = NULL;
			
				*pbRequireRediscovery = TRUE;
				return NULL;
			}
			
		}
		else
		{

			//further check for bRequireUpdate is not needed for this specific case
		}


	

		BOOL bEncounterCannotFindExchange = FALSE;

		tco_delete_list_tmp = olsr->recent_delete_list;
		//now it should not including the entry get to TCNode, since it is removed from the list,
		//so only those nodes reached (it is possible that nodes can be reached but consider TCNode as last hop)
		//by TCNode is remained 
		while (tco_delete_list_tmp != NULL)
		{


			rt_entry* prte = QueryRoutingTableAccordingToNodeId(node, tco_delete_list_tmp->nid);

			if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
			{
				uiLookupCnt++;
			}

			if (prte != NULL)
			{

				//prte->rt_entry_infos.bRequireExchange = FALSE;
				//prte->rt_entry_infos.bRequireUpdate = FALSE;
				prte->rt_entry_infos.bCostChanged = FALSE;
				prte->rt_entry_infos.bDescendentRequireFurtherUpdate = FALSE;
				//prteTC->rt_entry_infos.bRequireDelete = FALSE;

				prte->rt_entry_infos.uiCostChg = 0;

				if (prte->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 == olsr->naRecentChangedAddressByTC)
				{

					if (prte->rt_metric == 2)
					{
						neighbor_2_entry *two_hop_neighbor = NULL;

						two_hop_neighbor = OlsrLookup2HopNeighborTable(node, prte->rt_entry_infos.rtu_dst);

						if (two_hop_neighbor)
						{
							neighbor_list_entry* list_1 = NULL;

							list_1 = two_hop_neighbor->neighbor_2_nblist;

							BOOL b2HopNeighborCausedConnection = FALSE;
							while (list_1 != NULL)
							{
								if (list_1->neighbor->neighbor_main_addr.interfaceAddr.ipv4 == olsr->naRecentChangedAddressByTC)
								{
									b2HopNeighborCausedConnection = TRUE;
									break;
								}

								list_1 = list_1->neighbor_next;
							}

							if (b2HopNeighborCausedConnection)
							{


								//remove_from_tco_node_addr_set(&(olsr->recent_delete_list), tco_delete_list_tmp->nid);

								tco_delete_list_tmp = tco_delete_list_tmp->next;

								continue;
							}
						}
					}
					


					//prte->rt_entry_infos.bRequireExchange = TRUE;
					//prte->rt_entry_infos.bRequireUpdate = FALSE;
					
					BOOL bExchangeFound = FindRouteExchange(node, prte, FALSE, &uiLookupCnt);

					if (!bExchangeFound)
					{

						OlsrDeleteRoutingTable(prte);
						prte = NULL;

						*pbRequireRediscovery = TRUE;
						
						bEncounterCannotFindExchange = TRUE;

						break;
					}
					else
					{

						destination_n* list_destination_tmp;
						list_destination_tmp = (destination_n* )
							MEM_malloc(sizeof(destination_n));

						memset(
							list_destination_tmp,
							0,
							sizeof(destination_n));

						list_destination_tmp->destination = prte;
						list_destination_tmp->next = list_destination_n;
						list_destination_n = list_destination_tmp;
					}
				
				}
				else
				{
					//it is possible that nodes can be reached but not consider TCNode as last hop
					//skip these nodes

				}

			}
			else
			{

				//should not happen
			}


			tco_delete_list_tmp = tco_delete_list_tmp->next;
		}

		

		if (bEncounterCannotFindExchange)
		{

			//do Full Re-Calculation
			while (list_destination_n != NULL) 
			{

				destination_n* destination_n_1 = list_destination_n;
				list_destination_n = list_destination_n->next;
				MEM_free(destination_n_1);
			}

			list_destination_n = NULL;

			*pbRequireRediscovery = TRUE;

		
			if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
			{
				//uiLookupCnt++;
				*puiLookupCntForDeleteList = uiLookupCnt;
			}
			
			return NULL;

		}


		topology_last_entry * t_last_sym = OlsrLookupLastTopologyTableSYM(node, prteTC->rt_dst);
		if (t_last_sym != NULL && bExistReachTCFromTDNodeTBD)
		{

			destination_list* topo_dest = NULL;
			topo_dest = t_last_sym->topology_list_of_destinations;




			//rt_entry* prtetmpFormer = NULL;

			//BOOL bSameCostFormer = FALSE;
			//BOOL bCostPlusOneFormer = FALSE;

			//BOOL bExistSameCostWithSameRouterFormer = FALSE;

			while (topo_dest != NULL)
			{

				Address addrReached = topo_dest->destination_node->topology_destination_dst;


				topo_dest = topo_dest->next;

				rt_entry* prteNearby = QueryRoutingTableAccordingToNodeId(node, addrReached.interfaceAddr.ipv4);

				if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
				{
					uiLookupCnt++;
				}

				if (prteNearby != NULL)
				{


					//prteNearby->rt_entry_infos.bRequireExchange = FALSE;
					//prteNearby->rt_entry_infos.bRequireUpdate = FALSE;
					prteNearby->rt_entry_infos.bCostChanged = FALSE;
					prteNearby->rt_entry_infos.bDescendentRequireFurtherUpdate = FALSE;
					prteNearby->rt_entry_infos.bRequireDelete = FALSE;

					prteNearby->rt_entry_infos.uiCostChg = 0;



					if (prteNearby->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 == olsr->naRecentChangedAddressByTC)
					{

						//if (bExistReachTCFromTDNodeTBD)
						{

							if (prteTC->rt_entry_infos.bDescendentRequireFurtherUpdate)
							{

								if (prteTC->rt_entry_infos.bCostChanged)
								{

									//prteNearby->rt_entry_infos.bRequireExchange = TRUE;


									//prteNearby->rt_entry_infos.bRequireUpdate = FALSE;



									BOOL bExchangeFound = FindRouteExchange(node, prteNearby, TRUE, &uiLookupCnt);

									if (!bExchangeFound)
									{

										OlsrDeleteRoutingTable(prteNearby);
										prteNearby = NULL;

										*pbRequireRediscovery = TRUE;

										bEncounterCannotFindExchange = TRUE;

										break;
									}

								}
								else
								{
									//only route changed  

									//prteNearby->rt_entry_infos.bRequireExchange = FALSE;

									//prteNearby->rt_entry_infos.bRequireUpdate = TRUE;

									prteNearby->rt_interface = prteTC->rt_interface;
									prteNearby->rt_router = prteTC->rt_router;

									if (_OLSR_MULTIPATH)
									{



										prteNearby->rt_entry_infos.rtu_DegreeWRTNode = prteTC->rt_entry_infos.rtu_DegreeWRTNode;
										prteNearby->rt_entry_infos.rtu_DistanceWRTNode = prteTC->rt_entry_infos.rtu_DistanceWRTNode;
										prteNearby->rt_entry_infos.related_neighbor = prteTC->rt_entry_infos.related_neighbor;

									}


									prteNearby->rt_entry_infos.bDescendentRequireFurtherUpdate = TRUE;
									prteNearby->rt_entry_infos.bCostChanged = FALSE;
									prteNearby->rt_entry_infos.bRequireDelete = FALSE;

									prteNearby->rt_entry_infos.uiCostChg = 0;

								}
							}
						
						
							//add to list


							destination_n* list_destination_tmp;
							list_destination_tmp = (destination_n* )
								MEM_malloc(sizeof(destination_n));

							memset(
								list_destination_tmp,
								0,
								sizeof(destination_n));

							list_destination_tmp->destination = prteNearby;
							list_destination_tmp->next = list_destination_n;
							list_destination_n = list_destination_tmp;

						}
						/*
						else
						{

							//mean these nodes do not need to update wrt to the earlier exchange (the node that can reach TCNode) happened,
							//but just need to consider themselves

							

						}
						*/

					}

				

				
				}

			}


		}


		if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
		{
			//uiLookupCnt++;
			*puiLookupCntForDeleteList = uiLookupCnt;
		}

		if (bEncounterCannotFindExchange)
		{

			//do Full Re-Calculation
			while (list_destination_n != NULL) 
			{

				destination_n* destination_n_1 = list_destination_n;
				list_destination_n = list_destination_n->next;
				MEM_free(destination_n_1);
			}

			list_destination_n = NULL;

			*pbRequireRediscovery = TRUE;

			return NULL;

		}

	}
	else
	{
		//process for delete is not required 
	}


	
	return list_destination_n;
}



destination_n* ProcessRoutingTableAccordingToRecentDeleteListMP(Node* node, BOOL * pbRequireRediscovery, UInt32 * puiLookupCntForDeleteList)
{


	//DebugBreak();
	
	//printf("ProcessRoutingTableAccordingToRecentDeleteListMP \n");

	destination_n * list_destination_n = NULL;

	RoutingOlsr * olsr = (RoutingOlsr *) node->appData.olsr;

	tco_node_addr * tco_delete_list_tmp = olsr->recent_delete_list;			

	UInt32 uiLookupCnt = 0;

	*pbRequireRediscovery = FALSE;

	
	//if (tco_delete_list_tmp->nid == 10 && olsr->naRecentChangedAddressByTC == 15 && node->nodeId == 16)
	{

		//DebugBreak();
	}
	
	
	BOOL bCannotFindExchangeForAtLeastOneDest = FALSE;
	

	//prte and prteTC will exist or non-exist at the same time



	rthash * rhRetrieve = NULL;
	

	//	for ( ; prte != (rt_entry* ) rhRetrieve; prte = prte->rt_back)
	rt_entry* prteTC = QueryRoutingTableAccordingToNodeId(node, olsr->naRecentChangedAddressByTC, NULL, &rhRetrieve);
	

	if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
	{
		uiLookupCnt++;
	}

	if (prteTC != NULL)
	{

		for ( ; prteTC != (rt_entry* ) rhRetrieve; prteTC = prteTC->rt_back)
		{

			BOOL bExistReachTCFromTDNodeTBD = FALSE;

			//prteTC->rt_entry_infos.bRequireUpdate = FALSE;
			//prteTC->rt_entry_infos.bRequireExchange = FALSE;
			prteTC->rt_entry_infos.bDescendentRequireFurtherUpdate = FALSE;
			prteTC->rt_entry_infos.bCostChanged = FALSE;
			prteTC->rt_entry_infos.bRequireDelete = FALSE;

			prteTC->rt_entry_infos.uiCostChg = 0;


			tco_node_addr * ptna_set_tmp = NULL;

			tco_delete_list_tmp = olsr->recent_delete_list;

			while (tco_delete_list_tmp != NULL)
			{

				insert_into_tco_node_addr_set(&ptna_set_tmp, tco_delete_list_tmp->nid);


				tco_delete_list_tmp = tco_delete_list_tmp->next;
			}


			tco_delete_list_tmp = ptna_set_tmp;

			while (tco_delete_list_tmp != NULL)
			{
				
				if (prteTC->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 == tco_delete_list_tmp->nid)
				{

					//OlsrLookup2HopNeighborTable

					neighbor_2_entry *two_hop_neighbor = NULL;
					
					two_hop_neighbor = OlsrLookup2HopNeighborTable(node, prteTC->rt_entry_infos.rtu_dst);
					
					if (two_hop_neighbor)
					{
						neighbor_list_entry* list_1 = NULL;

						list_1 = two_hop_neighbor->neighbor_2_nblist;

						BOOL b2HopNeighborCausedConnection = FALSE;
						while (list_1 != NULL)
						{
							if (list_1->neighbor->neighbor_main_addr.interfaceAddr.ipv4 == tco_delete_list_tmp->nid)
							{
								b2HopNeighborCausedConnection = TRUE;
								break;
							}
							
							list_1 = list_1->neighbor_next;
						}

						if (b2HopNeighborCausedConnection)
						{
		

							remove_from_tco_node_addr_set(&(ptna_set_tmp), tco_delete_list_tmp->nid);

							break;
						}
					}


					bExistReachTCFromTDNodeTBD = TRUE;

					remove_from_tco_node_addr_set(&(ptna_set_tmp), tco_delete_list_tmp->nid);


					//prteTC->rt_entry_infos.bRequireUpdate = FALSE;
					
					//prteTC->rt_entry_infos.bRequireExchange = TRUE;

					

					break;
				}

				tco_delete_list_tmp = tco_delete_list_tmp->next;
			}


			if (bExistReachTCFromTDNodeTBD)
			//if (prteTC->rt_entry_infos.bRequireExchange)
			{

				//the same as bExistReachTCFromTDNodeTBD for this specific case

				//find exchange for this,
				//if can not find, then do not do following further exchange
				BOOL bExchangeFound = FindRouteExchange(node, prteTC, FALSE, &uiLookupCnt, TRUE);

				if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
				{
					
					*puiLookupCntForDeleteList = uiLookupCnt;
				}

				if (!bExchangeFound)
				{
					//comment: it seems unnecessary to delete since will re-discover
					//OlsrDeleteRoutingTable(prteTC);
					prteTC = NULL;
				
					*pbRequireRediscovery = TRUE;
					return NULL;
				}
				
			}
			else
			{

				//further check for bRequireUpdate is not needed for this specific case
			}



			BOOL bEncounterCannotFindExchange = FALSE;

			tco_delete_list_tmp = ptna_set_tmp;
			//now it should not including the entry get to TCNode, since it is removed from the list,
			//so only those nodes reached (it is possible that nodes can be reached but consider TCNode as last hop)
			//by TCNode is remained 
			while (tco_delete_list_tmp != NULL)
			{

				rt_entry* prteFirst = NULL;
				rt_entry* prte = QueryRoutingTableAccordingToNodeId(node, tco_delete_list_tmp->nid, &prteTC->rt_entry_infos.rtu_router.interfaceAddr.ipv4, NULL, &prteFirst);

				if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
				{
					uiLookupCnt++;
				}

				if (prte != NULL)
				{

					//prte->rt_entry_infos.bRequireExchange = FALSE;
					//prte->rt_entry_infos.bRequireUpdate = FALSE;

					prte->rt_entry_infos.uiCostChg = 0;

					prte->rt_entry_infos.bCostChanged = FALSE;
					prte->rt_entry_infos.bDescendentRequireFurtherUpdate = FALSE;
					prte->rt_entry_infos.bRequireDelete = FALSE;

					if (prte->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 == olsr->naRecentChangedAddressByTC)
					{


						neighbor_2_entry *two_hop_neighbor = NULL;

						two_hop_neighbor = OlsrLookup2HopNeighborTable(node, prte->rt_entry_infos.rtu_dst);

						if (two_hop_neighbor)
						{
							neighbor_list_entry* list_1 = NULL;

							list_1 = two_hop_neighbor->neighbor_2_nblist;

							BOOL b2HopNeighborCausedConnection = FALSE;
							while (list_1 != NULL)
							{
								if (list_1->neighbor->neighbor_main_addr.interfaceAddr.ipv4 == olsr->naRecentChangedAddressByTC)
								{
									b2HopNeighborCausedConnection = TRUE;
									break;
								}

								list_1 = list_1->neighbor_next;
							}

							if (b2HopNeighborCausedConnection)
							{


								//remove_from_tco_node_addr_set(&(olsr->recent_delete_list), tco_delete_list_tmp->nid);

								tco_delete_list_tmp = tco_delete_list_tmp->next;

								continue;
							}
						}


						//prte->rt_entry_infos.bRequireExchange = TRUE;
						//prte->rt_entry_infos.bRequireUpdate = FALSE;
						
						BOOL bExchangeFound = FindRouteExchange(node, prte, FALSE, &uiLookupCnt, TRUE);

						if (!bExchangeFound)
						{
							//seems unnecessary to delete
							
							if (prteFirst != NULL)
							{
								//if there is more than one entry for this dest, then it can be delete
								if (prteFirst->rt_entry_infos.oa_total_routes_count >= 2)
								{


									//OlsrDeleteRoutingTable(prte);

									
									 prteFirst->rt_entry_infos.oa_total_routes_count--;

									 if (prte != prteFirst)
									 {
										OlsrRemoveList((olsr_qelem *)prte);
										 //rt_entry* prteTmp = QueryRoutingTableAccordingToNodeId(node, tco_delete_list_tmp->nid);
									 }
									 else	//prte == prteFirst
									 {

										OlsrRemoveList((olsr_qelem *)prte);

										rt_entry* prteTmpNewFirst = QueryRoutingTableAccordingToNodeId(node, tco_delete_list_tmp->nid);

										if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
										{
											uiLookupCnt++;
										}

										if (prteTmpNewFirst != NULL)
										{

											prteTmpNewFirst->rt_entry_infos.oa_total_routes_count = prte->rt_entry_infos.oa_total_routes_count;
											prteTmpNewFirst->rt_entry_infos.oa_dWeightedDirectionDiffer = prte->rt_entry_infos.oa_dWeightedDirectionDiffer;
											prteTmpNewFirst->rt_entry_infos.oa_maximum_allowed_cost = prte->rt_entry_infos.oa_maximum_allowed_cost;

										}

									 }

									prte->rt_entry_infos.bRequireDelete = TRUE;
									prte->rt_entry_infos.bDescendentRequireFurtherUpdate = TRUE;

									destination_n* list_destination_tmp;
									list_destination_tmp = (destination_n* )
										MEM_malloc(sizeof(destination_n));

									memset(
										list_destination_tmp,
										0,
										sizeof(destination_n));

									list_destination_tmp->destination = prte;
									list_destination_tmp->next = list_destination_n;
									list_destination_n = list_destination_tmp;
									 
									
								}
								else	// < 2
								{
									
									//OlsrDeleteRoutingTable(prte);
									prte = NULL;




									*pbRequireRediscovery = TRUE;

									bEncounterCannotFindExchange = TRUE;

									break;
								}
							}
							else
							{
								//will never happen, since we have pre != NULL

							}

							
						}
						else
						{

							destination_n* list_destination_tmp;
							list_destination_tmp = (destination_n* )
								MEM_malloc(sizeof(destination_n));

							memset(
								list_destination_tmp,
								0,
								sizeof(destination_n));

							list_destination_tmp->destination = prte;
							list_destination_tmp->next = list_destination_n;
							list_destination_n = list_destination_tmp;
						}
					
					}
					else
					{
						//it is possible that nodes can be reached but not consider TCNode as last hop
						//skip these nodes

					}

				}
				else
				{

					//should not happen
				}


				tco_delete_list_tmp = tco_delete_list_tmp->next;
			}

			

			if (bEncounterCannotFindExchange)
			{

				//do Full Re-Calculation
				while (list_destination_n != NULL) 
				{

					destination_n* destination_n_1 = list_destination_n;
					list_destination_n = list_destination_n->next;
					MEM_free(destination_n_1);
				}

				list_destination_n = NULL;

				*pbRequireRediscovery = TRUE;

			
				if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
				{
					//uiLookupCnt++;
					*puiLookupCntForDeleteList = uiLookupCnt;
				}
				
				return NULL;

			}


			topology_last_entry * t_last_sym = OlsrLookupLastTopologyTableSYM(node, prteTC->rt_dst);
			if (t_last_sym != NULL && bExistReachTCFromTDNodeTBD)
			{

				destination_list* topo_dest = NULL;
				topo_dest = t_last_sym->topology_list_of_destinations;




				//rt_entry* prtetmpFormer = NULL;

				//BOOL bSameCostFormer = FALSE;
				//BOOL bCostPlusOneFormer = FALSE;

				//BOOL bExistSameCostWithSameRouterFormer = FALSE;

				while (topo_dest != NULL)
				{

					Address addrReached = topo_dest->destination_node->topology_destination_dst;


					topo_dest = topo_dest->next;

					rt_entry* prteNearby = QueryRoutingTableAccordingToNodeId(node, addrReached.interfaceAddr.ipv4, &prteTC->rt_entry_infos.rtu_router.interfaceAddr.ipv4, NULL);
					 
					if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
					{
						uiLookupCnt++;
					}

					if (prteNearby != NULL)
					{


						//prteNearby->rt_entry_infos.bRequireExchange = FALSE;
						//prteNearby->rt_entry_infos.bRequireUpdate = FALSE;
						prteNearby->rt_entry_infos.bCostChanged = FALSE;
						prteNearby->rt_entry_infos.bDescendentRequireFurtherUpdate = FALSE;
						prteNearby->rt_entry_infos.bRequireDelete = FALSE;

						prteNearby->rt_entry_infos.uiCostChg = 0;


						if (prteNearby->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 == olsr->naRecentChangedAddressByTC)
						{

							//if (bExistReachTCFromTDNodeTBD)
							{

								if (prteTC->rt_entry_infos.bDescendentRequireFurtherUpdate)
								{

									if (prteTC->rt_entry_infos.bCostChanged)
									{

										//prteNearby->rt_entry_infos.bRequireExchange = TRUE;

										//prteNearby->rt_entry_infos.bRequireUpdate = FALSE;

										BOOL bExchangeFound = FindRouteExchange(node, prteNearby, TRUE, &uiLookupCnt, TRUE);

										if (!bExchangeFound)
										{

											OlsrDeleteRoutingTable(prteNearby);
											prteNearby = NULL;

											*pbRequireRediscovery = TRUE;

											bEncounterCannotFindExchange = TRUE;

											break;
										}

									}
									else
									{
										//only route changed  

										//prteNearby->rt_entry_infos.bRequireExchange = FALSE;

										//prteNearby->rt_entry_infos.bRequireUpdate = TRUE;

										prteNearby->rt_interface = prteTC->rt_interface;
										prteNearby->rt_router = prteTC->rt_router;


										
										prteNearby->rt_entry_infos.rtu_DegreeWRTNode = prteTC->rt_entry_infos.rtu_DegreeWRTNode;
										prteNearby->rt_entry_infos.rtu_DistanceWRTNode = prteTC->rt_entry_infos.rtu_DistanceWRTNode;
										prteNearby->rt_entry_infos.related_neighbor = prteTC->rt_entry_infos.related_neighbor;

										prteNearby->rt_entry_infos.bDescendentRequireFurtherUpdate = TRUE;
										prteNearby->rt_entry_infos.bCostChanged = FALSE;
										prteNearby->rt_entry_infos.bRequireDelete = FALSE;

										prteNearby->rt_entry_infos.uiCostChg = 0;

									}
								}
							
							
								//add to list


								destination_n* list_destination_tmp;
								list_destination_tmp = (destination_n* )
									MEM_malloc(sizeof(destination_n));

								memset(
									list_destination_tmp,
									0,
									sizeof(destination_n));

								list_destination_tmp->destination = prteNearby;
								list_destination_tmp->next = list_destination_n;
								list_destination_n = list_destination_tmp;

							}
							/*
							else
							{

								//mean these nodes do not need to update wrt to the earlier exchange (the node that can reach TCNode) happened,
								//but just need to consider themselves

								

							}
							*/

						}
				
					}

				}

			}


			if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
			{
				//uiLookupCnt++;
				*puiLookupCntForDeleteList = uiLookupCnt;
			}

			if (bEncounterCannotFindExchange)
			{

				//do Full Re-Calculation
				while (list_destination_n != NULL) 
				{

					destination_n* destination_n_1 = list_destination_n;
					list_destination_n = list_destination_n->next;
					MEM_free(destination_n_1);
				}

				list_destination_n = NULL;

				*pbRequireRediscovery = TRUE;

				return NULL;

			}

		}

	}
	else
	{
		//process for delete is not required 
	}


	
	return list_destination_n;
}




destination_n* ProcessRoutingTableAccordingToRecentAddListV42(Node* node, UInt32 * puiLookupCntForAddList)
{
	destination_n* list_destination_n = NULL;

	RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;


	UInt32 uiLCFA = 0;


	if (remove_from_tco_node_addr_set(&olsr->recent_add_list, olsr->naRecentChangedAddressByTC))
	{
		//include the route itself and new 2hop neighbors are added

		if (olsr->bNeighborChgCausedRemoveFromHigherHop)
		{

			//exchange??
			//currently just use the most easy way that form the delete list

			tco_node_addr * disconnected_list = NULL;
			insert_into_tco_node_addr_set(&disconnected_list, olsr->naRecentChangedAddressByTC);

			tco_node_addr * destination_list_n_1 = disconnected_list;
			tco_node_addr * destination_list_n = disconnected_list;

			while (destination_list_n_1 != NULL)
			{
				destination_list_n_1 = NULL;

				topology_last_entry* topo_last = NULL;
				destination_list* topo_dest = NULL;


				//Peter comment: every loop add group of destination nodes that one hop more from the source node,
				//compare to the group in the previous loop  
				while (destination_list_n != NULL)
				{
					tco_node_addr* tna_tmp = NULL;

					Address addrCurrent;
					addrCurrent.networkType = NETWORK_IPV4;
					addrCurrent.interfaceAddr.ipv4 = destination_list_n->nid;

					//Peter comment: find from the topology table if there is some entry 
					//whose last hop equal the specific dest hop of 2 or more (* since every loop will
					// increase the one more hop count) hop neighbors
					if (SYMMETRIC_TOPOLOGY_TABLE)
					{
						topo_last = OlsrLookupLastTopologyTableSYM(node, addrCurrent);
					}
					else
					{
						topo_last = OlsrLookupLastTopologyTable(node, addrCurrent);
					}


					if (NULL != topo_last)
					{
						topo_dest = topo_last->topology_list_of_destinations;

						while (topo_dest != NULL)
						{

							Address addrReached = topo_dest->destination_node->topology_destination_dst;


							rt_entry* prte_tmp = QueryRoutingTableAccordingToNodeId(node, addrReached.interfaceAddr.ipv4);

							if (_TEST_TIME_COMPLEXITY && puiLookupCntForAddList)
							{
								uiLCFA++;
							}

							if (prte_tmp != NULL)
							{
								if (prte_tmp->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 == destination_list_n->nid)
								{
									insert_into_tco_node_addr_set(&(destination_list_n_1), addrReached.interfaceAddr.ipv4);

									OlsrDeleteRoutingTable(prte_tmp);

									insert_into_tco_node_addr_set(&(olsr->recent_delete_list), addrReached.interfaceAddr.ipv4);

								}
							}				


							topo_dest = topo_dest->next;
						}
					}

					tna_tmp = destination_list_n;
					destination_list_n = destination_list_n->next;
					MEM_free(tna_tmp);
				}

				destination_list_n = destination_list_n_1;

			}

			//so all the descendants of this old 2Hop neighbor were deleted, and traced in  olsr->recent_delete_list
		}

		if (olsr->recent_add_list == NULL)
		{
			OlsrFillRoutingTableWithSpecificNeighbor(node, olsr->naRecentChangedAddressByTC);
			//see ###$$$ in file Speed-10-6x6-low-TraceRT_SP_ARC_2_tmp15, a special case, may need further study

			//it seems it is possible for old un-used 2hop neighbor to exist (seems unreasonable, but do exist)
			list_destination_n = OlsrFillRoutingTableWith2HopNeighborsForSpecificNeighbor(node, olsr->naRecentChangedAddressByTC, &uiLCFA);
		}
		else
		{
			OlsrFillRoutingTableWithSpecificNeighbor(node, olsr->naRecentChangedAddressByTC);
			list_destination_n = OlsrFillRoutingTableWith2HopNeighborsForSpecificNeighbor(node, olsr->naRecentChangedAddressByTC, &uiLCFA);
		}


	}
	else
	{
		//only 2hop neighbors are new added

		list_destination_n = OlsrFillRoutingTableWith2HopNeighborsForSpecificNeighbor(node, olsr->naRecentChangedAddressByTC, &uiLCFA);


	}

	if (_TEST_TIME_COMPLEXITY && puiLookupCntForAddList != NULL)
	{
		*puiLookupCntForAddList += uiLCFA;
	}	


	return list_destination_n;
}



destination_n* ProcessRoutingTableAccordingToRecentAddListV46(Node* node, destination_n ** plist_destination_delete, UInt32 * puiLookupCntForAddList)
{

	destination_n* list_destination_n = NULL;

	RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;


	UInt32 uiLCFA = 0;


	if (remove_from_tco_node_addr_set(&olsr->recent_add_list, olsr->naRecentChangedAddressByTC))
	{
		//include the route itself and new 2hop neighbors are added


		UInt16 uiOldCostTC = MAX_COST;

		if (olsr->bNeighborChgCausedRemoveFromHigherHop)
		{

			rt_entry* prteTC = QueryRoutingTableAccordingToNodeId(node, olsr->naRecentChangedAddressByTC);


			if (_TEST_TIME_COMPLEXITY && puiLookupCntForAddList)
			{
				uiLCFA++;
			}
							

			if (prteTC != NULL)
			{

				uiOldCostTC = prteTC->rt_metric;

				//this should be true

				topology_last_entry* topo_last = NULL;
				destination_list* topo_dest = NULL;
				if (SYMMETRIC_TOPOLOGY_TABLE)
				{
					topo_last = OlsrLookupLastTopologyTableSYM(node, prteTC->rt_dst);
				}
				else
				{
					topo_last = OlsrLookupLastTopologyTable(node, prteTC->rt_dst);
				}


				if (NULL != topo_last)
				{
					topo_dest = topo_last->topology_list_of_destinations;

					while (topo_dest != NULL)
					{

						Address addrReached = topo_dest->destination_node->topology_destination_dst;

						topo_dest = topo_dest->next;

						BOOL b2HopNeighborCausedConnection = FALSE;

						b2HopNeighborCausedConnection = ConnectivetyCausedBy2HopNeighbor(node, addrReached, olsr->naRecentChangedAddressByTC);
						if (b2HopNeighborCausedConnection)
						{
							continue;
						}


						rt_entry* prte_tmp = QueryRoutingTableAccordingToNodeId(node, addrReached.interfaceAddr.ipv4);

						if (_TEST_TIME_COMPLEXITY && puiLookupCntForAddList)
						{
							uiLCFA++;
						}

						if (prte_tmp != NULL)
						{
							if (prte_tmp->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 == olsr->naRecentChangedAddressByTC)
							{
								//insert_into_tco_node_addr_set(&(destination_list_n_1), addrReached.interfaceAddr.ipv4);

								//OlsrDeleteRoutingTable(prte_tmp);

								//prte_tmp->rt_metric = MAX_COST;

								insert_into_tco_node_addr_set(&(olsr->recent_delete_list), addrReached.interfaceAddr.ipv4);
								//insert_into_tco_node_addr_set(&disconnected_list, addrReached.interfaceAddr.ipv4);

							}
						}				


					}
				}


			}


						
			

			//exchange??
			//currently just use the most easy way that form the delete list

			/*
			if (disconnected_list != NULL && prteTC->rt_metric > 2)
			{
				printf("********************************** disconnected_list != NULL, for node %d and olsr->naRecentChangedAddressByTC %d, with prteTC->rt_metric %d, include but not limit to %d \n", node->nodeId, olsr->naRecentChangedAddressByTC, prteTC->rt_metric, disconnected_list->nid);
			}
			*/


			

			//so all the descendants of this old 2Hop neighbor were deleted, and traced in  olsr->recent_delete_list
		}

		if (olsr->recent_add_list == NULL)
		{
			OlsrFillRoutingTableWithSpecificNeighbor(node, olsr->naRecentChangedAddressByTC);
			//see ###$$$ in file Speed-10-6x6-low-TraceRT_SP_ARC_2_tmp15, a special case, may need further study
			
			//it seems it is possible for old un-used 2hop neighbor to exist (seems unreasonable, but do exist)
			list_destination_n = OlsrFillRoutingTableWith2HopNeighborsForSpecificNeighbor(node, olsr->naRecentChangedAddressByTC, &uiLCFA);
		}
		else
		{
			OlsrFillRoutingTableWithSpecificNeighbor(node, olsr->naRecentChangedAddressByTC);
			list_destination_n = OlsrFillRoutingTableWith2HopNeighborsForSpecificNeighbor(node, olsr->naRecentChangedAddressByTC, &uiLCFA);
		}


		if (olsr->bNeighborChgCausedRemoveFromHigherHop) 
		{

			if (olsr->recent_delete_list != NULL)
			{

				

				//destination_n * list_p0_n = NULL;


				e2_s e2_plus_one;
				e2_s e2_plus_two;
				e2_s e2_plus_three;



				e2_plus_one.list_delete = NULL;
				e2_plus_one.list_p0 = NULL;
				e2_plus_one.list_p1 = NULL;
				e2_plus_one.list_p2 = NULL;


				e2_plus_two.list_delete = NULL;
				e2_plus_two.list_p0 = NULL;
				e2_plus_two.list_p1 = NULL;
				e2_plus_two.list_p2 = NULL;



				e2_plus_three.list_delete = NULL;
				e2_plus_three.list_p0 = NULL;
				e2_plus_three.list_p1 = NULL;
				e2_plus_three.list_p2 = NULL;





				e2_s e2s_n;
				e2_s e2s_n_1;

				e2s_n.list_delete = NULL;
				e2s_n.list_p0 = NULL;
				e2s_n.list_p1 = NULL;
				e2s_n.list_p2 = NULL;

				e2s_n_1.list_delete = NULL;
				e2s_n_1.list_p0 = NULL;
				e2s_n_1.list_p1 = NULL;
				e2s_n_1.list_p2 = NULL;
				
				
				//uiOldCostTC = 2 means the cost for nodes in current delete list = 3
				//if (list_destination_n != NULL && uiOldCostTC != 2)


				if (list_destination_n != NULL)
				{

					// we try to update the list_destination_n firstly

					UInt16 uiCurrentCost = 2; //for 2HopNeighbor
					destination_n* list_destination_n_1 = list_destination_n;

					while (list_destination_n_1 != NULL)
					{
						list_destination_n_1 = NULL;

						destination_n*  tmp_destination_tail = NULL;

						//Peter comment: every loop add group of destination nodes that one hop more from the source node,
						//compare to the group in the previous loop  
						while (list_destination_n != NULL)
						{
							destination_n* destination_n_1 = NULL;

							if (DEBUG)
							{
								char addrString[MAX_STRING_LENGTH];

								IO_ConvertIpAddressToString(
									&list_destination_n->destination->rt_dst,
									addrString);

								printf("Node %d, Last hop %s\n",
									node->nodeId,
									addrString);
							}

							topology_last_entry* topo_last = NULL;
							//Peter comment: find from the topology table if there is some entry 
							//whose last hop equal the specific dest hop of 2 or more (* since every loop will
							// increase the one more hop count) hop neighbors
							if (SYMMETRIC_TOPOLOGY_TABLE)
							{
								topo_last = OlsrLookupLastTopologyTableSYM(node, list_destination_n->destination->rt_dst);
							}
							else
							{
								topo_last = OlsrLookupLastTopologyTable(node, list_destination_n->destination->rt_dst);
							}


							if (NULL != topo_last)
							{
								destination_list* topo_dest = topo_last->topology_list_of_destinations;


								while (topo_dest != NULL)
								{

									Address addrReached = topo_dest->destination_node->topology_destination_dst;

									if (RoutingOlsrCheckMyIfaceAddress(
										node,
										topo_dest->destination_node->topology_destination_dst) != -1)
									{
										topo_dest = topo_dest->next;
										continue;
									}

									//destination_n* tmp_tmp_for_new_destination = NULL;
									OlsrCalculateRoutingTableForSinglePathTopologySearchHelpFunc(node, addrReached, list_destination_n, &list_destination_n_1, &tmp_destination_tail, TRUE);
									
														

									//uiOldCostTC + 1 is the current un-determined cost for these entry in delete list
									//(uiOldCostTC + 1) + 2) = uiOldCostTC + 3 means we allow +2 exchange so far
									if (uiCurrentCost <= (uiOldCostTC + 3))
									{
										if (tmp_destination_tail != NULL && olsr->recent_delete_list != NULL)
										{
											if (tmp_destination_tail->destination->rt_entry_infos.rtu_dst.interfaceAddr.ipv4 == addrReached.interfaceAddr.ipv4)
											{
												//the reached one is added or updated

												remove_from_tco_node_addr_set(&olsr->recent_delete_list, addrReached.interfaceAddr.ipv4);
											}
										}												
									}
									

									//Peter Added for test time complexity
									if (_TEST_TIME_COMPLEXITY)
									{

										//if (node->nodeId == NODE_ID_FOR_TEST_OUTER_ANGLE || node->nodeId == NODE_ID_FOR_TEST_OUTER_EDGE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_ANGLE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_EDGE || node->nodeId == NODE_ID_FOR_TEST_CENTER)
										if (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END)
										{
											uiLCFA++;

										}
									}

									topo_dest = topo_dest->next;
								}
							}

							destination_n_1 = list_destination_n;
							list_destination_n = list_destination_n->next;
							MEM_free(destination_n_1);
						}

						uiCurrentCost++;

						list_destination_n = list_destination_n_1;
						//ui_metric_cost_limitation++;
					}

				
				
				}
			

				//list_destination_n == NULL now !!!!!!
				if (olsr->recent_delete_list != NULL)			
				{

					tco_node_addr * tmp_recent_delete_list = NULL;

					tco_node_addr * tmp_addr = olsr->recent_delete_list;


					destination_n * p_destination_del = NULL;
					
					while (tmp_addr != NULL)
					{

						rt_entry* prte = QueryRoutingTableAccordingToNodeId(node, tmp_addr->nid);
						
						destination_n* list_destination_tmp;
						list_destination_tmp = (destination_n* )
							MEM_malloc(sizeof(destination_n));

						memset(
							list_destination_tmp,
							0,
							sizeof(destination_n));

						list_destination_tmp->destination = prte;
						
						list_destination_tmp->next = p_destination_del;
						p_destination_del = list_destination_tmp;

						//insert_into_tco_node_addr_set(&(tmp_recent_delete_list), tmp_addr->nid);

						tmp_addr = tmp_addr->next;
					}

					//tmp_addr = tmp_recent_delete_list;



					//exchange, since no other can reduce its cost

					//just try to exchange with same cost
					//and leave it to delete list otherwise

					destination_n * p_destination_del2 = NULL;

					{

						destination_n * p_destination_tmp = p_destination_del;
						while (p_destination_tmp != NULL)
						{

							rt_entry* prte = p_destination_tmp->destination;


							if (_TEST_TIME_COMPLEXITY && puiLookupCntForAddList)
							{
								uiLCFA++;
							}


							if (prte != NULL)
							{

								//the exchange here need to support unconsider set,
								//to avoid circular dependency 

								prte->rt_entry_infos.uiCostChg = 0;

								prte->rt_entry_infos.bCostChanged = FALSE;
								prte->rt_entry_infos.bDescendentRequireFurtherUpdate = FALSE;
								prte->rt_entry_infos.bRequireDelete = FALSE;


								BOOL bExchangeFound = FindRouteExchangeV20(node, p_destination_tmp, prte, FALSE, NULL);
								if (!bExchangeFound)
								{
									destination_n* list_destination_tmp;
									list_destination_tmp = (destination_n* )
										MEM_malloc(sizeof(destination_n));

									memset(
										list_destination_tmp,
										0,
										sizeof(destination_n));

									list_destination_tmp->destination = prte;

									{
										list_destination_tmp->children = p_destination_tmp->children;
										list_destination_tmp->bChildrenDetermined = p_destination_tmp->bChildrenDetermined;

										p_destination_tmp->children = NULL;
									}



									//only route change
									list_destination_tmp->next = p_destination_del2;
									p_destination_del2 = list_destination_tmp;

								}
								else
								{
									
									remove_from_tco_node_addr_set(&(olsr->recent_delete_list), prte->rt_entry_infos.rtu_dst.interfaceAddr.ipv4);

									if (prte->rt_entry_infos.bDescendentRequireFurtherUpdate)
									{

										//route change

										destination_n* list_destination_tmp;
										list_destination_tmp = (destination_n* )
											MEM_malloc(sizeof(destination_n));

										memset(
											list_destination_tmp,
											0,
											sizeof(destination_n));

										list_destination_tmp->destination = prte;

										{
											list_destination_tmp->children = p_destination_tmp->children;
											list_destination_tmp->bChildrenDetermined = p_destination_tmp->bChildrenDetermined;

											p_destination_tmp->children = NULL;
										}


										//only route change
										list_destination_tmp->next = e2_plus_one.list_p0;
										e2_plus_one.list_p0 = list_destination_tmp;

									
									}
									else
									{
										//perfect exchange
										
									}

								}
							}

							destination_n * destination_n_1 = p_destination_tmp;						
							p_destination_tmp = p_destination_tmp->next;

							MEM_free(destination_n_1);
						}


						/*
						if (tmp_recent_delete_list != NULL)
						{
							clear_tco_node_addr_set(&tmp_recent_delete_list);
						}
						*/

					}




					//backup for 22 exchange  for +2
					tco_node_addr * disconnected_list_backup = NULL;
					tco_node_addr * tmp_addr2 = olsr->recent_delete_list;
					while (tmp_addr2 != NULL)
					{

						insert_into_tco_node_addr_set(&(disconnected_list_backup), tmp_addr2->nid);
						tmp_addr2 = tmp_addr2->next;
					}


					destination_n * p_destination_del3 = NULL;
					{

						// need to find whether  can be exchanged by +1, since all +0 (list_destination_TS_plus_one) are determined

						//tco_node_addr * tmp_disconnected_list = NULL;

						if (olsr->recent_delete_list != NULL)
						{

							//while (disconnected_list != NULL)
							{

								//copy the set

								/*
								tco_node_addr * tmp_addr = olsr->recent_delete_list;
								while (tmp_addr != NULL)
								{

									insert_into_tco_node_addr_set(&(tmp_disconnected_list), tmp_addr->nid);
									tmp_addr = tmp_addr->next;
								}

								tco_node_addr * tmp_addr_tmp = tmp_disconnected_list;
								*/

								//BOOL bAtleastFindOne = FALSE;
								destination_n * p_destination_tmp = p_destination_del2;
								while (p_destination_tmp != NULL)
								{

									//rt_entry* prte = QueryRoutingTableAccordingToNodeId(node, tmp_addr_tmp->nid);

									rt_entry* prte = p_destination_tmp->destination;

									if (_TEST_TIME_COMPLEXITY && puiLookupCntForAddList)
									{
										uiLCFA++;
									}
									

									if (prte != NULL)
									{

										//the exchange here need to support unconsider set,
										//to avoid circular dependency 

										prte->rt_entry_infos.uiCostChg = 0;

										prte->rt_entry_infos.bCostChanged = FALSE;
										prte->rt_entry_infos.bDescendentRequireFurtherUpdate = FALSE;
										prte->rt_entry_infos.bRequireDelete = FALSE;


										BOOL bExchangeFound = FindRouteExchangeV21(node, p_destination_tmp, prte, FALSE, NULL, &uiLCFA, FALSE, &olsr->recent_delete_list, NULL, NULL, 
											&disconnected_list_backup);
										if (!bExchangeFound)
										{

											destination_n* list_destination_tmp;
											list_destination_tmp = (destination_n* )
												MEM_malloc(sizeof(destination_n));

											memset(
												list_destination_tmp,
												0,
												sizeof(destination_n));

											list_destination_tmp->destination = prte;

											{
												list_destination_tmp->children = p_destination_tmp->children;
												list_destination_tmp->bChildrenDetermined = p_destination_tmp->bChildrenDetermined;

												p_destination_tmp->children = NULL;
											}



											//only route change
											list_destination_tmp->next = p_destination_del3;
											p_destination_del3 = list_destination_tmp;



										}
										else
										{

											remove_from_tco_node_addr_set(&(olsr->recent_delete_list), prte->rt_entry_infos.rtu_dst.interfaceAddr.ipv4);
											//insert_into_tco_node_addr_set(&(found_list), tmp_addr_tmp->nid);

											//bAtleastFindOne = TRUE;

											if (prte->rt_entry_infos.bDescendentRequireFurtherUpdate)
											{

												if (prte->rt_entry_infos.uiCostChg == 1)
												{
													destination_n* list_destination_tmp;
													list_destination_tmp = (destination_n* )
														MEM_malloc(sizeof(destination_n));

													memset(
														list_destination_tmp,
														0,
														sizeof(destination_n));

													list_destination_tmp->destination = prte;

													{
														list_destination_tmp->children = p_destination_tmp->children;
														list_destination_tmp->bChildrenDetermined = p_destination_tmp->bChildrenDetermined;

														p_destination_tmp->children = NULL;
													}


													list_destination_tmp->next = e2_plus_two.list_p1;
													e2_plus_two.list_p1 = list_destination_tmp;

												}
												else
												{
													//should not happen
												}

											}
											else
											{
												//perfect exchange
												//should not happen
											}

										}
									}

									//p_destination_tmp = p_destination_tmp->next;

									destination_n * destination_n_1 = p_destination_tmp;						
									p_destination_tmp = p_destination_tmp->next;

									MEM_free(destination_n_1);
								}


								/*
								if (tmp_disconnected_list != NULL)
								{
									clear_tco_node_addr_set(&tmp_disconnected_list);
								}
								*/

							}


						}
						else
						{
							//
						}


					}



					//deal with children of list_destination_TS_plus_one_p0

					UInt32 uiInnerExchangeLUCnt = 0;

					SubFuncForLoopHelpFuncV22(node, (&e2_plus_one.list_p0), NULL, NULL, &e2_plus_two, &uiInnerExchangeLUCnt, &(olsr->recent_delete_list));

					if (_TEST_TIME_COMPLEXITY && puiLookupCntForAddList)
					{
						
						uiLCFA += uiInnerExchangeLUCnt;

					}

		

					uiInnerExchangeLUCnt = 0;

					if (g_iToAchieveSameRoute == 1)
					{
						
						destination_n* list_avoid_consider_for_p1 = NULL;
						tco_node_addr* tco_avoid_consider_list_p1 = NULL;


						//p1 list, +0 exchange
						if (e2_plus_two.list_p1 != NULL)
						{

							while (e2_plus_two.list_p1 != NULL)
							{

								destination_n* destination_n_1 = NULL;
								destination_list* topo_dest = NULL;
								
								if (e2_plus_two.list_p1->bChildrenDetermined)
								{
									destination_n * dst_child = e2_plus_two.list_p1->children;
									while (dst_child != NULL)
									{


										Address addrReached = dst_child->destination->rt_entry_infos.rtu_dst;							

										UInt32 uiInnerExchangeLUCnt = 0;

										OlsrCalculateRoutingTableForSinglePathTopologySearchHelpFuncV24(node, dst_child, addrReached, e2_plus_two.list_p1, &e2_plus_two.list_p0, 
											&list_avoid_consider_for_p1, &uiInnerExchangeLUCnt, &tco_avoid_consider_list_p1, &olsr->recent_delete_list);

										dst_child = dst_child->next;
									}
								}
								else
								{
									topology_last_entry* topo_last = OlsrLookupLastTopologyTableSYM(node, e2_plus_two.list_p1->destination->rt_dst);

									if (NULL != topo_last)
									{
										topo_dest = topo_last->topology_list_of_destinations;

										while (topo_dest != NULL)
										{

											Address addrReached = topo_dest->destination_node->topology_destination_dst;							

											UInt32 uiInnerExchangeLUCnt = 0;

											OlsrCalculateRoutingTableForSinglePathTopologySearchHelpFuncV24(node, NULL, addrReached, e2_plus_two.list_p1, &e2_plus_two.list_p0, 
												&list_avoid_consider_for_p1, &uiInnerExchangeLUCnt, &tco_avoid_consider_list_p1, &olsr->recent_delete_list);

											topo_dest = topo_dest->next;
										}
									}

								}
								


								destination_n_1 = e2_plus_two.list_p1;
								e2_plus_two.list_p1 = e2_plus_two.list_p1->next;
								MEM_free(destination_n_1);
							}


						}




						if (list_avoid_consider_for_p1 != NULL)
						{

							while (list_avoid_consider_for_p1 != NULL)
							{

								destination_n* destination_n_1 = NULL;

								
								if (_TEST_TIME_COMPLEXITY && puiLookupCntForAddList)
								{

									uiLCFA ++;

								}


								//while (topo_dest != NULL)
								{

									Address addrReached = list_avoid_consider_for_p1->destination->rt_dst;

									UInt32 uiInnerExchangeLUCnt = 0;

									rt_entry* preExisting = list_avoid_consider_for_p1->destination;


									preExisting->rt_entry_infos.bCostChanged = FALSE;
									preExisting->rt_entry_infos.bDescendentRequireFurtherUpdate = FALSE;
									preExisting->rt_entry_infos.bRequireDelete = FALSE;

									preExisting->rt_entry_infos.uiCostChg = 0;


									BOOL bExchangeFound = FindRouteExchangeV21(node, list_avoid_consider_for_p1, preExisting, TRUE, NULL, &uiInnerExchangeLUCnt, FALSE, &tco_avoid_consider_list_p1, &olsr->recent_delete_list, 
										NULL, &disconnected_list_backup);
									
									if (!bExchangeFound)
									{

										//should certainly find

									}
									else
									{
										if (preExisting->rt_entry_infos.bDescendentRequireFurtherUpdate)
										{

											destination_n* list_destination_tmp;
											list_destination_tmp = (destination_n* )
												MEM_malloc(sizeof(destination_n));

											memset(
												list_destination_tmp,
												0,
												sizeof(destination_n));

											//list_destination_tmp->destination = preExisting;

											list_destination_tmp->destination = preExisting;

											{
												list_destination_tmp->children = list_avoid_consider_for_p1->children;
												list_destination_tmp->bChildrenDetermined = list_avoid_consider_for_p1->bChildrenDetermined;

												list_avoid_consider_for_p1->children = NULL;
											}

											list_destination_tmp->next = e2_plus_three.list_p1;
											e2_plus_three.list_p1 = list_destination_tmp;


											//+1 case								

										}

									}								

								}



								destination_n_1 = list_avoid_consider_for_p1;
								list_avoid_consider_for_p1 = list_avoid_consider_for_p1->next;


								remove_from_tco_node_addr_set(&tco_avoid_consider_list_p1, destination_n_1->destination->rt_entry_infos.rtu_dst.interfaceAddr.ipv4);

								MEM_free(destination_n_1);			


							}

						}


						clear_tco_node_addr_set(&tco_avoid_consider_list_p1);
						
					}
					else
					{

						SubFuncForLoopHelpFuncV22(node, (&e2_plus_two.list_p1), &e2_plus_one, &e2_plus_two, &e2_plus_three, &uiInnerExchangeLUCnt, &olsr->recent_delete_list);

					}




					destination_n * p_destination_del4 = NULL;
					{

						// need to find whether DATS can be exchanged by +2, since all +1 (till list_destination_TS_plus_two) are determined

						//tco_node_addr * tmp_disconnected_list = NULL;

						if (olsr->recent_delete_list != NULL)
						{

							//while (disconnected_list != NULL)
							{

								//copy the set

								/*
								tco_node_addr * tmp_addr = olsr->recent_delete_list;
								while (tmp_addr != NULL)
								{

									insert_into_tco_node_addr_set(&(tmp_disconnected_list), tmp_addr->nid);
									tmp_addr = tmp_addr->next;
								}

								tco_node_addr * tmp_addr_tmp = tmp_disconnected_list;
								*/

								//BOOL bAtleastFindOne = FALSE;

								destination_n * p_destination_tmp = p_destination_del3;

								while (p_destination_tmp != NULL)
								{

									//rt_entry* prte = QueryRoutingTableAccordingToNodeId(node, tmp_addr_tmp->nid);

									rt_entry* prte = p_destination_tmp->destination;

									if (_TEST_TIME_COMPLEXITY && puiLookupCntForAddList)
									{

										uiLCFA ++;

									}

									if (prte != NULL)
									{

										//the exchange here need to support unconsider set,
										//to avoid circular dependency 

										prte->rt_entry_infos.uiCostChg = 0;

										prte->rt_entry_infos.bCostChanged = FALSE;
										prte->rt_entry_infos.bDescendentRequireFurtherUpdate = FALSE;
										prte->rt_entry_infos.bRequireDelete = FALSE;


										BOOL bExchangeFound = FindRouteExchangeV22(node, p_destination_tmp, prte, FALSE, NULL, &uiLCFA, FALSE, &olsr->recent_delete_list, NULL, &disconnected_list_backup);
										if (!bExchangeFound)
										{
											destination_n* list_destination_tmp;
											list_destination_tmp = (destination_n* )
												MEM_malloc(sizeof(destination_n));

											memset(
												list_destination_tmp,
												0,
												sizeof(destination_n));

											list_destination_tmp->destination = prte;

											{
												list_destination_tmp->children = p_destination_tmp->children;
												list_destination_tmp->bChildrenDetermined = p_destination_tmp->bChildrenDetermined;

												p_destination_tmp->children = NULL;
											}



											//only route change
											list_destination_tmp->next = p_destination_del4;
											p_destination_del4 = list_destination_tmp;

										}
										else
										{

											remove_from_tco_node_addr_set(&(olsr->recent_delete_list), prte->rt_entry_infos.rtu_dst.interfaceAddr.ipv4);
											//insert_into_tco_node_addr_set(&(found_list), tmp_addr_tmp->nid);

											//bAtleastFindOne = TRUE;

											if (prte->rt_entry_infos.bDescendentRequireFurtherUpdate)
											{

												if (prte->rt_entry_infos.uiCostChg == 2)
												{
													destination_n* list_destination_tmp;
													list_destination_tmp = (destination_n* )
														MEM_malloc(sizeof(destination_n));

													memset(
														list_destination_tmp,
														0,
														sizeof(destination_n));

													list_destination_tmp->destination = prte;

													{
														list_destination_tmp->children = p_destination_tmp->children;
														list_destination_tmp->bChildrenDetermined = p_destination_tmp->bChildrenDetermined;

														p_destination_tmp->children = NULL;
													}


													list_destination_tmp->next = e2_plus_three.list_p2;
													e2_plus_three.list_p2 = list_destination_tmp;

												}
												else
												{
													//should not happen
												}

											}
											else
											{
												//perfect exchange
												//should not happen
											}

										}
									}

									destination_n * destination_n_1 = p_destination_tmp;						
									p_destination_tmp = p_destination_tmp->next;

									MEM_free(destination_n_1);
								}


								/*
								if (tmp_disconnected_list != NULL)
								{
									clear_tco_node_addr_set(&tmp_disconnected_list);
								}
								*/

							}


						}
						else
						{
							//
						}


					}

					clear_tco_node_addr_set(&disconnected_list_backup);


					//tco_node_addr * tna_tmp = olsr->recent_delete_list;
					
					destination_n * p_destination_tmp = p_destination_del4;
					while (p_destination_tmp != NULL)
					{

						//rt_entry* prte = QueryRoutingTableAccordingToNodeId(node, tna_tmp->nid);
						rt_entry* prte = p_destination_tmp->destination;

						prte->rt_metric = MAX_COST;

						
						destination_n* list_destination_tmp;
						list_destination_tmp = (destination_n* )
							MEM_malloc(sizeof(destination_n));

						memset(
							list_destination_tmp,
							0,
							sizeof(destination_n));

						list_destination_tmp->destination = prte;

						
						{
							list_destination_tmp->children = p_destination_tmp->children;
							list_destination_tmp->bChildrenDetermined = p_destination_tmp->bChildrenDetermined;

							p_destination_tmp->children = NULL;
						}
											


						list_destination_tmp->next = e2_plus_one.list_delete;
						e2_plus_one.list_delete = list_destination_tmp;

						
						
						//p_destination_tmp = p_destination_tmp->next;

						destination_n * destination_n_1 = p_destination_tmp;						
						p_destination_tmp = p_destination_tmp->next;

						MEM_free(destination_n_1);
					}


					clear_tco_node_addr_set(&olsr->recent_delete_list);


					//destination_n* list_destination_delete = NULL;

					DeleteListProgress(node, &e2_plus_one, &e2_plus_two, &olsr->recent_delete_list, plist_destination_delete);

					
					DeleteListProgress(node, &e2_plus_two, &e2_plus_three, &olsr->recent_delete_list, plist_destination_delete);



					//destination_n * list_n_minus_1_p0 = NULL;

					tco_node_addr * tco_avoid_consider_list = NULL;
					destination_n * list_avoid_consider_for_p2 = NULL;



					uiInnerExchangeLUCnt = 0;
					SubFuncForLoopHelpFuncV23(node, e2_plus_three, &e2_plus_two.list_p0, &list_avoid_consider_for_p2, &uiInnerExchangeLUCnt, &tco_avoid_consider_list);

					if (_TEST_TIME_COMPLEXITY && puiLookupCntForAddList)
					{

						uiLCFA += uiInnerExchangeLUCnt;

					}
							
					uiInnerExchangeLUCnt = 0;

					SubFuncForLoopHelpFuncV22(node, (&e2_plus_two.list_p0), NULL, NULL, &e2_plus_three, &uiInnerExchangeLUCnt, &tco_avoid_consider_list);

					if (_TEST_TIME_COMPLEXITY && puiLookupCntForAddList)
					{

						uiLCFA += uiInnerExchangeLUCnt;

					}


					ProcessRecurrentPlus2(node, uiOldCostTC + 3, &tco_avoid_consider_list, &olsr->recent_delete_list, e2_plus_three, &list_avoid_consider_for_p2, plist_destination_delete, &uiLCFA);
				



					clear_tco_node_addr_set(&tco_avoid_consider_list);			



				}				

			}
			else
			{
				//no further process required, since the following update discovery will deal with all TC's old children

			}

		}


	}
	else
	{
		//only 2hop neighbors are new added

		list_destination_n = OlsrFillRoutingTableWith2HopNeighborsForSpecificNeighbor(node, olsr->naRecentChangedAddressByTC, &uiLCFA);

		
	}

	if (_TEST_TIME_COMPLEXITY && puiLookupCntForAddList != NULL)
	{
		*puiLookupCntForAddList += uiLCFA;
	}	


	return list_destination_n;
}


//void ProcessRecurrentPlus2(Node* node, tco_node_addr * tco_avoid_consider_list, tco_node_addr ** ptna_delete, UInt32 * puiLookupCntForDeleteList, destination_n* list_to_delete, e2_s e2_plus_three, destination_n *  list_avoid_consider_for_p2, destination_n & list_destination_delete)
void ProcessRecurrentPlus2(Node* node, UInt16 uiStartCost, tco_node_addr ** ptco_avoid_consider_list, tco_node_addr ** ptna_delete, e2_s e2_plus_three, destination_n ** plist_avoid_consider_for_p2, destination_n ** list_destination_delete, UInt32 * puiLookupCntForDeleteList)
{

		e2_s e2_s_n;
		e2_s e2_s_n_1;

		UInt32 uiInnerExchangeLUCnt = 0;

		UInt16 uiLookupCnt = 0;


		//e2_s_n_minus_1.list_delete = e2_plus_two.list_delete;
		//e2_s_n_minus_1.list_p0 = e2_plus_two.list_p0;
		//e2_s_n_minus_1.list_p1 = e2_plus_two.list_p1;
		//e2_s_n_minus_1.list_p2 = e2_plus_two.list_p2;


		e2_s_n.list_delete = e2_plus_three.list_delete;
		e2_s_n.list_p0 = e2_plus_three.list_p0;
		e2_s_n.list_p1 = e2_plus_three.list_p1;
		e2_s_n.list_p2 = e2_plus_three.list_p2;

		e2_s_n_1.list_delete = e2_s_n.list_delete;
		e2_s_n_1.list_p0 = e2_s_n.list_p0;
		e2_s_n_1.list_p1 = e2_s_n.list_p1;
		e2_s_n_1.list_p2 = e2_s_n.list_p2;



	

		while (e2_s_n_1.list_delete != NULL || e2_s_n_1.list_p0 != NULL || e2_s_n_1.list_p1 != NULL || e2_s_n_1.list_p2 != NULL || *plist_avoid_consider_for_p2 != NULL)
		{


			e2_s_n_1.list_delete = NULL;
			e2_s_n_1.list_p0 = NULL;
			e2_s_n_1.list_p1 = NULL;
			e2_s_n_1.list_p2 = NULL;



			destination_n* list_destination_recent_delete = NULL;
			destination_n* tmp_last_destination = NULL;


			//deal with delete list
			/*
			if (e2_s_n.list_delete)
			{

				while (e2_s_n.list_delete != NULL)
				{
					//DebugBreak();
					destination_n* destination_n_1 = NULL;
					destination_list* topo_dest = NULL;
					topology_last_entry* topo_last = OlsrLookupLastTopologyTableSYM(node, e2_s_n.list_delete->destination->rt_dst);
					if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
					{
						uiLookupCnt++;
					}


					BOOL bInsideNode = TRUE;

					destination_n* list_destination_tmp_children = NULL;

					if (NULL != topo_last)
					{
						topo_dest = topo_last->topology_list_of_destinations;

						while (topo_dest != NULL)
						{

							Address addrReached = topo_dest->destination_node->topology_destination_dst;

						

							UInt32 uiInnerExchangeLUCnt = 0;


							
							rt_entry* prteNearby = QueryRoutingTableAccordingToNodeId(node, addrReached.interfaceAddr.ipv4);
							if (prteNearby != NULL)
							{

								if (prteNearby->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 == e2_s_n.list_delete->destination->rt_entry_infos.rtu_dst.interfaceAddr.ipv4)
								{


									prteNearby->rt_metric = MAX_COST;

									destination_n* list_destination_tmp;
									list_destination_tmp = (destination_n* )
										MEM_malloc(sizeof(destination_n));

									memset(
										list_destination_tmp,
										0,
										sizeof(destination_n));

									list_destination_tmp->destination = prteNearby;
									

									//list_destination_tmp->next = e2_s_n_1.list_delete;
									//e2_s_n_1.list_delete = list_destination_tmp;

									//TO_IMPROVE_PERFORMANCE
									list_destination_tmp->next = e2_s_n.list_delete->children;
									e2_s_n.list_delete->children = list_destination_tmp;


									
									//insert_into_tco_node_addr_set(&(destination_list_n_1), addrReached.interfaceAddr.ipv4);

									//OlsrDeleteRoutingTable(prte_tmp);

									//insert_into_tco_node_addr_set(&(olsr->recent_add_list), addrReached.interfaceAddr.ipv4);



								}
								else
								{
									if (e2_s_n.list_delete->destination->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 == prteNearby->rt_entry_infos.rtu_dst.interfaceAddr.ipv4)
									{


									}
									else
									{

										//if there is any other adjacent nodes outside the tree, then 

										bInsideNode = FALSE;

									}
								}
							
							}
							
							//OlsrCalculateRoutingTableForSinglePathTopologySearchHelpFuncV22(node, addrReached, e2_plus_one.list_p0, &e2_plus_one, &e2_plus_two, &e2_plus_three, &uiInnerExchangeLUCnt, &ATS_list, &disconnected_list);


							//Peter Added for test time complexity
							if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
							{
								uiLookupCnt += uiInnerExchangeLUCnt;

								//if (node->nodeId == NODE_ID_FOR_TEST_OUTER_ANGLE || node->nodeId == NODE_ID_FOR_TEST_OUTER_EDGE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_ANGLE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_EDGE || node->nodeId == NODE_ID_FOR_TEST_CENTER)
								if (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END)
								{
									uiLookupCnt++;

								}
							}

							topo_dest = topo_dest->next;
						}
					}

					destination_n_1 = e2_s_n.list_delete;
					e2_s_n.list_delete = e2_s_n.list_delete->next;
					//MEM_free(destination_n_1);

					if (!bInsideNode)
					{
						insert_into_tco_node_addr_set(ptna_delete, destination_n_1->destination->rt_entry_infos.rtu_dst.interfaceAddr.ipv4);

					}
					

					//TO_IMPROVE_PERFORMANCE
					
					destination_n_1->next = list_destination_recent_delete;
					list_destination_recent_delete = destination_n_1;

					if (tmp_last_destination == NULL)
					{
						tmp_last_destination = list_destination_recent_delete;
					}
					
					

					//destination_n_1->next = *list_destination_delete;
					//*list_destination_delete = destination_n_1;
				}
			}
			*/


			destination_n * list_avoid_consider_for_p2_remain = NULL;

			tco_node_addr * tmp_tco_avoid_consider_list = NULL;

			
			if (*plist_avoid_consider_for_p2 != NULL)
			{						

				if (g_iToAchieveSameRoute == 1)
				{

					tco_node_addr * tmp_addr = *ptco_avoid_consider_list;
					while (tmp_addr != NULL)
					{

						insert_into_tco_node_addr_set(&(tmp_tco_avoid_consider_list), tmp_addr->nid);
						tmp_addr = tmp_addr->next;
					}
				}

				
				while (*plist_avoid_consider_for_p2 != NULL)
				{

					BOOL bNotDeleteForSameRouteSP = FALSE;
					//DebugBreak();
					destination_n* destination_n_1 = NULL;
					//destination_list* topo_dest = NULL;
					//topology_last_entry* topo_last = OlsrLookupLastTopologyTableSYM(node, list_avoid_consider_for_p2->destination->rt_dst);
					if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
					{
						uiLookupCnt++;
					}

					//if (NULL != topo_last)
					{
						//topo_dest = topo_last->topology_list_of_destinations;

						//while (topo_dest != NULL)
						{

							Address addrReached = (*plist_avoid_consider_for_p2)->destination->rt_dst;

							UInt32 uiInnerExchangeLUCnt = 0;
						
							rt_entry* preExisting = (*plist_avoid_consider_for_p2)->destination;

							
							preExisting->rt_entry_infos.bCostChanged = FALSE;
							preExisting->rt_entry_infos.bDescendentRequireFurtherUpdate = FALSE;
							preExisting->rt_entry_infos.bRequireDelete = FALSE;

							preExisting->rt_entry_infos.uiCostChg = 0;

							BOOL bExchangeFound = FindRouteExchangeV21(node, *plist_avoid_consider_for_p2, preExisting, FALSE, NULL, &uiInnerExchangeLUCnt, FALSE, ptco_avoid_consider_list, NULL, NULL, &tmp_tco_avoid_consider_list);

							if (!bExchangeFound)
							{

								if (g_iToAchieveSameRoute == 1)
								{
									bNotDeleteForSameRouteSP = TRUE;
								}
								else
								{
									destination_n* list_destination_tmp;
									list_destination_tmp = (destination_n* )
										MEM_malloc(sizeof(destination_n));

									memset(
										list_destination_tmp,
										0,
										sizeof(destination_n));

									//list_destination_tmp->destination = preExisting;

									//
									preExisting->rt_metric = preExisting->rt_metric + 2;

									preExisting->rt_entry_infos.bCostChanged = TRUE;
									preExisting->rt_entry_infos.bDescendentRequireFurtherUpdate = TRUE;


									preExisting->rt_entry_infos.uiCostChg = 2;

									list_destination_tmp->destination = preExisting;

									
									{
										list_destination_tmp->children = (*plist_avoid_consider_for_p2)->children;
										list_destination_tmp->bChildrenDetermined = (*plist_avoid_consider_for_p2)->bChildrenDetermined;

										(*plist_avoid_consider_for_p2)->children = NULL;
									}

									list_destination_tmp->next = e2_s_n_1.list_p2;
									e2_s_n_1.list_p2 = list_destination_tmp;
								}


							}
							else
							{
								if (preExisting->rt_entry_infos.bDescendentRequireFurtherUpdate)
								{

									destination_n* list_destination_tmp;
									list_destination_tmp = (destination_n* )
										MEM_malloc(sizeof(destination_n));

									memset(
										list_destination_tmp,
										0,
										sizeof(destination_n));

									//list_destination_tmp->destination = preExisting;

									list_destination_tmp->destination = preExisting;


									{
										list_destination_tmp->children = (*plist_avoid_consider_for_p2)->children;
										list_destination_tmp->bChildrenDetermined = (*plist_avoid_consider_for_p2)->bChildrenDetermined;

										(*plist_avoid_consider_for_p2)->children = NULL;
									}



									list_destination_tmp->next = e2_s_n.list_p1;
									e2_s_n.list_p1 = list_destination_tmp;
								

									//+1 case								
									
								}
								/*
								else
								{
									preExisting = NULL;
								}
								*/
							}



							//Peter Added for test time complexity
							if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
							{
								uiLookupCnt += uiInnerExchangeLUCnt;

								//if (node->nodeId == NODE_ID_FOR_TEST_OUTER_ANGLE || node->nodeId == NODE_ID_FOR_TEST_OUTER_EDGE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_ANGLE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_EDGE || node->nodeId == NODE_ID_FOR_TEST_CENTER)
								if (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END)
								{
									uiLookupCnt++;

								}
							}

							//topo_dest = topo_dest->next;
						}
					}


					destination_n_1 = *plist_avoid_consider_for_p2;
					*plist_avoid_consider_for_p2 = (*plist_avoid_consider_for_p2)->next;
					
					if (g_iToAchieveSameRoute == 1 && bNotDeleteForSameRouteSP)
					{
						
						destination_n_1->next = list_avoid_consider_for_p2_remain;
						list_avoid_consider_for_p2_remain = destination_n_1;
					}
					else
					{
						
						if (g_iToAchieveSameRoute == 1)
						{
							
							remove_from_tco_node_addr_set(ptco_avoid_consider_list, destination_n_1->destination->rt_entry_infos.rtu_dst.interfaceAddr.ipv4);
						}

						MEM_free(destination_n_1);
					
					}					
					
				}

			}



			if (g_iToAchieveSameRoute == 1)
			{

			}
			else
			{
				clear_tco_node_addr_set(ptco_avoid_consider_list);
			}

			
			destination_n * list_avoid_consider_for_p1 = NULL;
			tco_node_addr * tco_avoid_consider_list_p1 = NULL;



			uiInnerExchangeLUCnt = 0;

			if (g_iToAchieveSameRoute == 1)
			{

				//p1 list, +0 exchange
				if (e2_s_n.list_p1 != NULL)
				{
								
					while (e2_s_n.list_p1 != NULL)
					{
				
						destination_n* destination_n_1 = NULL;
						destination_list* topo_dest = NULL;
						
						if (e2_s_n.list_p1->bChildrenDetermined)
						{
							
							destination_n * dst_child = e2_s_n.list_p1->children;
							while (dst_child != NULL)
							{
								

								Address addrReached = dst_child->destination->rt_entry_infos.rtu_dst;							

								UInt32 uiInnerExchangeLUCnt = 0;

								OlsrCalculateRoutingTableForSinglePathTopologySearchHelpFuncV24(node, dst_child, addrReached, e2_s_n.list_p1, &e2_s_n.list_p0, 
									&list_avoid_consider_for_p1, &uiInnerExchangeLUCnt, &tco_avoid_consider_list_p1, ptco_avoid_consider_list);

								dst_child = dst_child->next;
							}
						}
						else
						{

							topology_last_entry* topo_last = OlsrLookupLastTopologyTableSYM(node, e2_s_n.list_p1->destination->rt_dst);

							if (NULL != topo_last)
							{
								topo_dest = topo_last->topology_list_of_destinations;

								while (topo_dest != NULL)
								{

									Address addrReached = topo_dest->destination_node->topology_destination_dst;							

									UInt32 uiInnerExchangeLUCnt = 0;

									OlsrCalculateRoutingTableForSinglePathTopologySearchHelpFuncV24(node, NULL, addrReached, e2_s_n.list_p1, &e2_s_n.list_p0, 
										&list_avoid_consider_for_p1, &uiInnerExchangeLUCnt, &tco_avoid_consider_list_p1, ptco_avoid_consider_list);

									topo_dest = topo_dest->next;
								}
							}
						}
						
						

						destination_n_1 = e2_s_n.list_p1;
						e2_s_n.list_p1 = e2_s_n.list_p1->next;
						MEM_free(destination_n_1);
					}
				
				
				}




				if (list_avoid_consider_for_p1 != NULL)
				{
								
					while (list_avoid_consider_for_p1 != NULL)
					{
						
						destination_n* destination_n_1 = NULL;
					
						if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
						{
							uiLookupCnt++;
						}
						
							
						//while (topo_dest != NULL)
						{

							Address addrReached = list_avoid_consider_for_p1->destination->rt_dst;

							UInt32 uiInnerExchangeLUCnt = 0;
						
							rt_entry* preExisting = list_avoid_consider_for_p1->destination;

							
							preExisting->rt_entry_infos.bCostChanged = FALSE;
							preExisting->rt_entry_infos.bDescendentRequireFurtherUpdate = FALSE;
							preExisting->rt_entry_infos.bRequireDelete = FALSE;

							preExisting->rt_entry_infos.uiCostChg = 0;


							BOOL bExchangeFound = FindRouteExchangeV21(node, list_avoid_consider_for_p1, preExisting, TRUE, NULL, &uiInnerExchangeLUCnt, FALSE, ptco_avoid_consider_list, &tco_avoid_consider_list_p1, NULL, &tmp_tco_avoid_consider_list);
							if (!bExchangeFound)
							{

								//should certainly find

							}
							else
							{
								if (preExisting->rt_entry_infos.bDescendentRequireFurtherUpdate)
								{

									destination_n* list_destination_tmp;
									list_destination_tmp = (destination_n* )
										MEM_malloc(sizeof(destination_n));

									memset(
										list_destination_tmp,
										0,
										sizeof(destination_n));

									//list_destination_tmp->destination = preExisting;

									list_destination_tmp->destination = preExisting;

									{
										list_destination_tmp->children = list_avoid_consider_for_p1->children;
										list_destination_tmp->bChildrenDetermined = list_avoid_consider_for_p1->bChildrenDetermined;

										list_avoid_consider_for_p1->children = NULL;
									}

									list_destination_tmp->next = e2_s_n_1.list_p1;
									e2_s_n_1.list_p1 = list_destination_tmp;
								

									//+1 case								
									
								}
								
							}



							//Peter Added for test time complexity
							if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
							{
								uiLookupCnt += uiInnerExchangeLUCnt;

								//if (node->nodeId == NODE_ID_FOR_TEST_OUTER_ANGLE || node->nodeId == NODE_ID_FOR_TEST_OUTER_EDGE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_ANGLE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_EDGE || node->nodeId == NODE_ID_FOR_TEST_CENTER)
								if (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END)
								{
									uiLookupCnt++;

								}
							}
						
						}
						


						destination_n_1 = list_avoid_consider_for_p1;
						list_avoid_consider_for_p1 = list_avoid_consider_for_p1->next;
												
						
						remove_from_tco_node_addr_set(&tco_avoid_consider_list_p1, destination_n_1->destination->rt_entry_infos.rtu_dst.interfaceAddr.ipv4);
						
						MEM_free(destination_n_1);			
								
						
					}

				}


				clear_tco_node_addr_set(&tco_avoid_consider_list_p1);


				//+2 exchange for +2 list
				if (list_avoid_consider_for_p2_remain != NULL)
				{
								
					while (list_avoid_consider_for_p2_remain != NULL)
					{

						
						//DebugBreak();
						destination_n* destination_n_1 = NULL;
						//destination_list* topo_dest = NULL;
						//topology_last_entry* topo_last = OlsrLookupLastTopologyTableSYM(node, list_avoid_consider_for_p2->destination->rt_dst);
						if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
						{
							uiLookupCnt++;
						}

						//if (NULL != topo_last)
						{
							//topo_dest = topo_last->topology_list_of_destinations;

							//while (topo_dest != NULL)
							{

								Address addrReached = list_avoid_consider_for_p2_remain->destination->rt_dst;

								UInt32 uiInnerExchangeLUCnt = 0;
							
								rt_entry* preExisting = list_avoid_consider_for_p2_remain->destination;

								
								preExisting->rt_entry_infos.bCostChanged = FALSE;
								preExisting->rt_entry_infos.bDescendentRequireFurtherUpdate = FALSE;
								preExisting->rt_entry_infos.bRequireDelete = FALSE;

								preExisting->rt_entry_infos.uiCostChg = 0;

								BOOL bExchangeFound = FindRouteExchangeV22(node, list_avoid_consider_for_p2_remain, preExisting, TRUE, NULL, &uiInnerExchangeLUCnt, FALSE, ptco_avoid_consider_list, NULL, &tmp_tco_avoid_consider_list);
								
								if (!bExchangeFound)
								{

									//should find one

								}
								else
								{
									if (preExisting->rt_entry_infos.bDescendentRequireFurtherUpdate)
									{

										destination_n* list_destination_tmp;
										list_destination_tmp = (destination_n* )
											MEM_malloc(sizeof(destination_n));

										memset(
											list_destination_tmp,
											0,
											sizeof(destination_n));

										//list_destination_tmp->destination = preExisting;

										list_destination_tmp->destination = preExisting;

										{
											list_destination_tmp->children = list_avoid_consider_for_p2_remain->children;
											list_destination_tmp->bChildrenDetermined = list_avoid_consider_for_p2_remain->bChildrenDetermined;

											list_avoid_consider_for_p2_remain->children = NULL;
										}


										list_destination_tmp->next = e2_s_n_1.list_p2;
										e2_s_n_1.list_p2 = list_destination_tmp;
									

										//+2 case								
										
									}
									
								}



								//Peter Added for test time complexity
								if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
								{
									uiLookupCnt += uiInnerExchangeLUCnt;

									//if (node->nodeId == NODE_ID_FOR_TEST_OUTER_ANGLE || node->nodeId == NODE_ID_FOR_TEST_OUTER_EDGE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_ANGLE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_EDGE || node->nodeId == NODE_ID_FOR_TEST_CENTER)
									if (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END)
									{
										uiLookupCnt++;

									}
								}

								//topo_dest = topo_dest->next;
							}
						}

						destination_n_1 = list_avoid_consider_for_p2_remain;
						list_avoid_consider_for_p2_remain = list_avoid_consider_for_p2_remain->next;

						//remove_from_tco_node_addr_set(&tco_avoid_consider_list, destination_n_1->destination->rt_entry_infos.rtu_dst.interfaceAddr.ipv4);

						MEM_free(destination_n_1);						
												
					}

				}

				clear_tco_node_addr_set(ptco_avoid_consider_list);
				clear_tco_node_addr_set(&tmp_tco_avoid_consider_list);				

			}
			else
			{

				SubFuncForLoopHelpFuncV22(node, (&e2_s_n.list_p1), NULL, &e2_s_n, &e2_s_n_1, &uiInnerExchangeLUCnt);
			}




			/*
			//delete exchange for 0

			//TO_IMPROVE_PERFORMANCE
			//list_destination_tmp->next = e2_s_n_1.list_delete;
			//e2_s_n_1.list_delete = list_destination_tmp;
			
			if (tmp_last_destination != NULL)
			{
				//tmp_last_destination = list_destination_recent_delete;

				destination_n* tmp_dst = NULL;

				destination_n* p_tail = NULL;
				destination_n* p_tail_p0 = NULL;

				tmp_dst = list_destination_recent_delete;

				while (tmp_dst != NULL)
				{
					
					{
						//tmp_dst->destination->rt_entry_infos.rtu_metric = MAX_COST;

						if (e2_s_n_1.list_delete == NULL)
						{
							if (tmp_dst->children != NULL)
							{

								e2_s_n_1.list_delete = tmp_dst->children;
								//*p_tmp_destination_tail = destination_n_1;
								
								p_tail = e2_s_n_1.list_delete;
								
								while (p_tail->next != NULL)
								{
									p_tail = p_tail->next;
								}
							}
						
						}
						else
						{

							if (tmp_dst->children != NULL)
							{
								p_tail->next = tmp_dst->children;

								while (p_tail->next != NULL)
								{
									p_tail = p_tail->next;
								}
							}						

							//(*p_tmp_destination_tail)->next = destination_n_1;
							//*p_tmp_destination_tail = (*p_tmp_destination_tail)->next;

							//(*p_list_destination_n_1)->next = destination_n_1;
						}


						tmp_dst->children = NULL;
					}




					tmp_dst = tmp_dst->next;
				}



				tmp_last_destination->next = *list_destination_delete;
				*list_destination_delete = list_destination_recent_delete;
				
			}
			*/


			/*
			if (e2_s_n.list_delete != NULL)
			{
				destination_n * tmp_destination = NULL;

				tmp_destination = e2_s_n.list_delete;

				while (tmp_destination != NULL)
				{
			
					destination_n* destination_n_1 = NULL;
					destination_list* topo_dest = NULL;
					
					if (tmp_destination->bChildrenDetermined)
					{

						destination_n * dst_child = tmp_destination->children;
						while (dst_child != NULL)
						{

							Address addrReached = dst_child->destination->rt_entry_infos.rtu_dst;							

							UInt32 uiInnerExchangeLUCnt = 0;

							OlsrCalculateRoutingTableForSinglePathTopologySearchHelpFuncV23(node, dst_child, e2_s_n, addrReached, tmp_destination, e2_s_n.list_p0, NULL, &uiInnerExchangeLUCnt, NULL);

							
							dst_child = dst_child->next;
						}
					}
					else
					{

						topology_last_entry* topo_last = OlsrLookupLastTopologyTableSYM(node, tmp_destination->destination->rt_dst);
					

						if (NULL != topo_last)
						{

							topo_dest = topo_last->topology_list_of_destinations;
							while (topo_dest != NULL)
							{

								Address addrReached = topo_dest->destination_node->topology_destination_dst;


								UInt32 uiInnerExchangeLUCnt = 0;
							
								OlsrCalculateRoutingTableForSinglePathTopologySearchHelpFuncV23(node, NULL, e2_s_n, addrReached, tmp_destination, e2_s_n.list_p0, NULL, &uiInnerExchangeLUCnt, NULL);

							
								topo_dest = topo_dest->next;
							}
						}
					}
								

					tmp_destination = tmp_destination->next;
				
				}

				
				while (e2_current.list_p2 != NULL)
				{
					destination_n* destination_n_1 = NULL;
					destination_n_1 = e2_current.list_p2;
					e2_current.list_p2 = e2_current.list_p2->next;
					MEM_free(destination_n_1);
				}
				

			}
			*/

			
			

			DeleteListProgress(node, &e2_s_n, &e2_s_n_1, ptna_delete, list_destination_delete);

			

			if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
			{
				uiLookupCnt += uiInnerExchangeLUCnt;
			}


		


			uiInnerExchangeLUCnt = 0;
			SubFuncForLoopHelpFuncV23(node, e2_s_n_1, &e2_s_n.list_p0, plist_avoid_consider_for_p2, &uiInnerExchangeLUCnt, ptco_avoid_consider_list);

			if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
			{
				uiLookupCnt += uiInnerExchangeLUCnt;
			}


			

			uiInnerExchangeLUCnt = 0;

			SubFuncForLoopHelpFuncV22(node, (&e2_s_n.list_p0), NULL, NULL,  &e2_s_n_1, &uiInnerExchangeLUCnt, ptco_avoid_consider_list);

			if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
			{
				uiLookupCnt += uiInnerExchangeLUCnt;
			}


		
			uiStartCost++;

			e2_s_n.list_delete = e2_s_n_1.list_delete;
			e2_s_n.list_p0 = e2_s_n_1.list_p0;
			e2_s_n.list_p1 = e2_s_n_1.list_p1;
			e2_s_n.list_p2 = e2_s_n_1.list_p2;
			

		}



		clear_tco_node_addr_set(ptco_avoid_consider_list);


}


destination_n* ProcessRoutingTableAccordingToRecentAddListV45(Node* node, UInt32 * puiLookupCntForAddList)
{
	destination_n* list_destination_n = NULL;

	RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;


	UInt32 uiLCFA = 0;


	if (remove_from_tco_node_addr_set(&olsr->recent_add_list, olsr->naRecentChangedAddressByTC))
	{
		//include the route itself and new 2hop neighbors are added


		UInt16 uiOldCostTC = MAX_COST;

		if (olsr->bNeighborChgCausedRemoveFromHigherHop)
		{

			rt_entry* prteTC = QueryRoutingTableAccordingToNodeId(node, olsr->naRecentChangedAddressByTC);


			if (_TEST_TIME_COMPLEXITY && puiLookupCntForAddList)
			{
				uiLCFA++;
			}
							

			if (prteTC != NULL)
			{

				uiOldCostTC = prteTC->rt_metric;

				//this should be true

				topology_last_entry* topo_last = NULL;
				destination_list* topo_dest = NULL;
				if (SYMMETRIC_TOPOLOGY_TABLE)
				{
					topo_last = OlsrLookupLastTopologyTableSYM(node, prteTC->rt_dst);
				}
				else
				{
					topo_last = OlsrLookupLastTopologyTable(node, prteTC->rt_dst);
				}


				if (NULL != topo_last)
				{
					topo_dest = topo_last->topology_list_of_destinations;

					while (topo_dest != NULL)
					{

						Address addrReached = topo_dest->destination_node->topology_destination_dst;



						topo_dest = topo_dest->next;

						BOOL b2HopNeighborCausedConnection = FALSE;

						b2HopNeighborCausedConnection = ConnectivetyCausedBy2HopNeighbor(node, addrReached, olsr->naRecentChangedAddressByTC);
						if (b2HopNeighborCausedConnection)
						{
							continue;
						}


						rt_entry* prte_tmp = QueryRoutingTableAccordingToNodeId(node, addrReached.interfaceAddr.ipv4);

						if (_TEST_TIME_COMPLEXITY && puiLookupCntForAddList)
						{
							uiLCFA++;
						}

						if (prte_tmp != NULL)
						{
							if (prte_tmp->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 == olsr->naRecentChangedAddressByTC)
							{
								//insert_into_tco_node_addr_set(&(destination_list_n_1), addrReached.interfaceAddr.ipv4);

								//OlsrDeleteRoutingTable(prte_tmp);

								//prte_tmp->rt_metric = MAX_COST;

								insert_into_tco_node_addr_set(&(olsr->recent_delete_list), addrReached.interfaceAddr.ipv4);
								//insert_into_tco_node_addr_set(&disconnected_list, addrReached.interfaceAddr.ipv4);

							}
						}				


					}
				}


			}


						
			

			//exchange??
			//currently just use the most easy way that form the delete list

			/*
			if (disconnected_list != NULL && prteTC->rt_metric > 2)
			{
				printf("********************************** disconnected_list != NULL, for node %d and olsr->naRecentChangedAddressByTC %d, with prteTC->rt_metric %d, include but not limit to %d \n", node->nodeId, olsr->naRecentChangedAddressByTC, prteTC->rt_metric, disconnected_list->nid);
			}
			*/


			

			//so all the descendants of this old 2Hop neighbor were deleted, and traced in  olsr->recent_delete_list
		}

		if (olsr->recent_add_list == NULL)
		{
			OlsrFillRoutingTableWithSpecificNeighbor(node, olsr->naRecentChangedAddressByTC);
			//see ###$$$ in file Speed-10-6x6-low-TraceRT_SP_ARC_2_tmp15, a special case, may need further study
			
			//it seems it is possible for old un-used 2hop neighbor to exist (seems unreasonable, but do exist)
			list_destination_n = OlsrFillRoutingTableWith2HopNeighborsForSpecificNeighbor(node, olsr->naRecentChangedAddressByTC, &uiLCFA);
		}
		else
		{
			OlsrFillRoutingTableWithSpecificNeighbor(node, olsr->naRecentChangedAddressByTC);
			list_destination_n = OlsrFillRoutingTableWith2HopNeighborsForSpecificNeighbor(node, olsr->naRecentChangedAddressByTC, &uiLCFA);
		}


		if (olsr->bNeighborChgCausedRemoveFromHigherHop) 
		{

			if (olsr->recent_delete_list != NULL)
			{

				tco_node_addr * tmp_recent_delete_list = NULL;
				
				tco_node_addr * tmp_addr = olsr->recent_delete_list;
				
				
				
				while (tmp_addr != NULL)
				{

					insert_into_tco_node_addr_set(&(tmp_recent_delete_list), tmp_addr->nid);

					tmp_addr = tmp_addr->next;
				}

				tmp_addr = tmp_recent_delete_list;


				//destination_n * list_p0_n = NULL;
				e2_s e2s_n;
				e2_s e2s_n_1;

				e2s_n.list_delete = NULL;
				e2s_n.list_p0 = NULL;
				e2s_n.list_p1 = NULL;
				e2s_n.list_p2 = NULL;

				e2s_n_1.list_delete = NULL;
				e2s_n_1.list_p0 = NULL;
				e2s_n_1.list_p1 = NULL;
				e2s_n_1.list_p2 = NULL;
				
				
				//uiOldCostTC = 2 means the cost for nodes in current delete list = 3
				if (list_destination_n != NULL && uiOldCostTC != 2)
				{

					//just let them to be deleted
				
				}
				else
				{

					//exchange, since no other can reduce its cost

					//just try to exchange with same cost
					//and leave it to delete list otherwise

					

					{


						while (tmp_addr != NULL)
						{

							rt_entry* prte = QueryRoutingTableAccordingToNodeId(node, tmp_addr->nid);


							if (_TEST_TIME_COMPLEXITY && puiLookupCntForAddList)
							{
								uiLCFA++;
							}


							if (prte != NULL)
							{

								//the exchange here need to support unconsider set,
								//to avoid circular dependency 

								prte->rt_entry_infos.uiCostChg = 0;

								prte->rt_entry_infos.bCostChanged = FALSE;
								prte->rt_entry_infos.bDescendentRequireFurtherUpdate = FALSE;
								prte->rt_entry_infos.bRequireDelete = FALSE;


								BOOL bExchangeFound = FindRouteExchangeV20(node, NULL, prte, FALSE, NULL);
								if (!bExchangeFound)
								{


								}
								else
								{

									
									remove_from_tco_node_addr_set(&(olsr->recent_delete_list), tmp_addr->nid);

									if (prte->rt_entry_infos.bDescendentRequireFurtherUpdate)
									{

										//route change

										destination_n* list_destination_tmp;
										list_destination_tmp = (destination_n* )
											MEM_malloc(sizeof(destination_n));

										memset(
											list_destination_tmp,
											0,
											sizeof(destination_n));

										list_destination_tmp->destination = prte;



										//only route change

										list_destination_tmp->next = e2s_n.list_p0;
										e2s_n.list_p0 = list_destination_tmp;

									
									}
									else
									{
										//perfect exchange
										
									}

								}
							}

							tmp_addr = tmp_addr->next;
						}



					}

				}
				
				
				
				//if (list_destination_n != NULL)
				{
					

					
					/*
					while (tmp_addr != NULL)
					{
						destination_n* tmp_destination = list_destination_n;

						while (tmp_destination != NULL)
						{

							topology_last_entry* topo_last = NULL;
							destination_list* topo_dest = NULL;

							topo_last = OlsrLookupLastTopologyTableSYM(node, tmp_destination->destination->rt_dst);

							if (NULL != topo_last)
							{
								topo_dest = topo_last->topology_list_of_destinations;

								while (topo_dest != NULL)
								{

									Address addrReached = topo_dest->destination_node->topology_destination_dst;

									if (addrReached.interfaceAddr.ipv4 == tmp_addr->nid)
									{

										
									}

									topo_dest = topo_dest->next;
								}
							}

							tmp_destination = tmp_destination->next;
						}
						
				
						tmp_addr = tmp_addr->next;
					}
					*/
				 
				}
				
				
				
				if (tmp_recent_delete_list != NULL)
				{
					clear_tco_node_addr_set(&tmp_recent_delete_list);
				}
				

				tmp_addr = olsr->recent_delete_list;


				destination_n * list_delete_n = NULL;
				destination_n * list_delete_n_1 = NULL;
				
				while (tmp_addr != NULL)
				{

					
					rt_entry* prtetmp = QueryRoutingTableAccordingToNodeId(node, tmp_addr->nid);


					if (_TEST_TIME_COMPLEXITY && puiLookupCntForAddList)
					{
						uiLCFA++;
					}

					if (prtetmp != NULL)
					{
						
						//
						//prtetmp->rt_metric = MAX_COST;

						
						destination_n* list_destination_tmp;
						list_destination_tmp = (destination_n* )
							MEM_malloc(sizeof(destination_n));

						memset(
							list_destination_tmp,
							0,
							sizeof(destination_n));

						list_destination_tmp->destination = prtetmp;


						list_destination_tmp->next = list_delete_n;
						list_delete_n = list_destination_tmp;

						
						//OlsrDeleteRoutingTable(prtetmp);
					}
					
					tmp_addr = tmp_addr->next;
				}

				
				clear_tco_node_addr_set(&olsr->recent_delete_list);
				
				
				

				//list_delete_n = NULL;
				list_delete_n_1 = list_delete_n;

				if (list_delete_n != NULL)
				{

					while (list_delete_n_1 != NULL)
					{
						list_delete_n_1 = NULL;



						while (list_delete_n != NULL)
						{
							//DebugBreak();
							destination_n* destination_n_1 = NULL;
							destination_list* topo_dest = NULL;
							topology_last_entry* topo_last = OlsrLookupLastTopologyTableSYM(node, list_delete_n->destination->rt_dst);
							
							/*
							if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
							{
								uiLookupCnt++;
							}
							*/


							BOOL bInsideNode = TRUE;

							if (NULL != topo_last)
							{
								topo_dest = topo_last->topology_list_of_destinations;

								while (topo_dest != NULL)
								{

									Address addrReached = topo_dest->destination_node->topology_destination_dst;

									/*
									if (RoutingOlsrCheckMyIfaceAddress(
										node,
										topo_dest->destination_node->topology_destination_dst) != -1)
									{
										topo_dest = topo_dest->next;
										continue;
									}
									*/


									UInt32 uiInnerExchangeLUCnt = 0;
									
									rt_entry* prteNearby = QueryRoutingTableAccordingToNodeId(node, addrReached.interfaceAddr.ipv4);

									if (_TEST_TIME_COMPLEXITY && puiLookupCntForAddList)
									{
										uiLCFA++;
									}

									if (prteNearby != NULL)
									{

										if (prteNearby->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 == list_delete_n->destination->rt_entry_infos.rtu_dst.interfaceAddr.ipv4)
										{


											//prteNearby->rt_metric = MAX_COST;

											destination_n* list_destination_tmp;
											list_destination_tmp = (destination_n* )
												MEM_malloc(sizeof(destination_n));

											memset(
												list_destination_tmp,
												0,
												sizeof(destination_n));

											list_destination_tmp->destination = prteNearby;
											

											list_destination_tmp->next = list_delete_n_1;
											list_delete_n_1 = list_destination_tmp;
											
											//insert_into_tco_node_addr_set(&(destination_list_n_1), addrReached.interfaceAddr.ipv4);

											//OlsrDeleteRoutingTable(prte_tmp);

											//insert_into_tco_node_addr_set(&(olsr->recent_add_list), addrReached.interfaceAddr.ipv4);

										}
										else
										{
											if (list_delete_n->destination->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 == prteNearby->rt_entry_infos.rtu_dst.interfaceAddr.ipv4)
											{


											}
											else
											{

												//if there is any other adjacent nodes outside the tree, then 

												bInsideNode = FALSE;

											}
										}
									
									}
									
						

									topo_dest = topo_dest->next;
								}
							}

							destination_n_1 = list_delete_n;
							list_delete_n = list_delete_n->next;
							//MEM_free(destination_n_1);

							if (!bInsideNode)
							{

								insert_into_tco_node_addr_set(&olsr->recent_delete_list, destination_n_1->destination->rt_entry_infos.rtu_dst.interfaceAddr.ipv4);
							}

							OlsrDeleteRoutingTable(destination_n_1->destination);
							MEM_free(destination_n_1);
							

						}


						list_delete_n = list_delete_n_1;

					}
									
				}



				if (e2s_n.list_p0 != NULL)
				{

					//destination_n * list_p0_n_1 = list_p0_n;
					e2s_n_1.list_p0 = e2s_n.list_p0;

					while (e2s_n_1.list_p0 != NULL)
					{

						e2s_n_1.list_p0 = NULL;				

						while (e2s_n.list_p0 != NULL)
						{
							//DebugBreak();
							destination_n* destination_n_1 = NULL;
							destination_list* topo_dest = NULL;
							topology_last_entry* topo_last = OlsrLookupLastTopologyTableSYM(node, e2s_n.list_p0->destination->rt_dst);
							
							/*
							if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
							{
								uiLookupCnt++;
							}
							*/

							if (NULL != topo_last)
							{
								topo_dest = topo_last->topology_list_of_destinations;

								while (topo_dest != NULL)
								{

									Address addrReached = topo_dest->destination_node->topology_destination_dst;

									/*
									if (RoutingOlsrCheckMyIfaceAddress(
										node,
										topo_dest->destination_node->topology_destination_dst) != -1)
									{
										topo_dest = topo_dest->next;
										continue;
									}
									*/


									UInt32 uiInnerExchangeLUCnt = 0;



									OlsrCalculateRoutingTableForSinglePathTopologySearchHelpFuncV22(node, NULL, addrReached, e2s_n.list_p0, NULL, NULL, &e2s_n_1, &uiInnerExchangeLUCnt);


									if (_TEST_TIME_COMPLEXITY && puiLookupCntForAddList)
									{
										uiLCFA += uiInnerExchangeLUCnt;
									}

									//Peter Added for test time complexity
									/*
									if (_TEST_TIME_COMPLEXITY && puiLookupCntForDeleteList)
									{
										uiLookupCnt += uiInnerExchangeLUCnt;

										//if (node->nodeId == NODE_ID_FOR_TEST_OUTER_ANGLE || node->nodeId == NODE_ID_FOR_TEST_OUTER_EDGE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_ANGLE || node->nodeId == NODE_ID_FOR_TEST_MIDDLE_EDGE || node->nodeId == NODE_ID_FOR_TEST_CENTER)
										if (node->nodeId >= NODE_ID_FOR_TEST_START && node->nodeId <= NODE_ID_FOR_TEST_END)
										{
											uiLookupCnt++;

										}
									}
									*/

									topo_dest = topo_dest->next;
								}
							}

							destination_n_1 = e2s_n.list_p0;
							e2s_n.list_p0 = e2s_n.list_p0->next;
							MEM_free(destination_n_1);
						}


						e2s_n.list_p0 = e2s_n_1.list_p0;
					}

					
				}


				

			}
			else
			{
				//no further process required, since the following update discovery will deal with all TC's old children

			}

		}


	}
	else
	{
		//only 2hop neighbors are new added

		list_destination_n = OlsrFillRoutingTableWith2HopNeighborsForSpecificNeighbor(node, olsr->naRecentChangedAddressByTC, &uiLCFA);

		
	}

	if (_TEST_TIME_COMPLEXITY && puiLookupCntForAddList != NULL)
	{
		*puiLookupCntForAddList += uiLCFA;
	}	


	return list_destination_n;
}



destination_n* ProcessRoutingTableAccordingToRecentAddListV44(Node* node, UInt32 * puiLookupCntForAddList)
{

	destination_n* list_destination_n = NULL;

	RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;


	UInt32 uiLCFA = 0;


	if (remove_from_tco_node_addr_set(&olsr->recent_add_list, olsr->naRecentChangedAddressByTC))
	{
		//include the route itself and new 2hop neighbors are added


		UInt16 uiOldCostTC = MAX_COST;

		if (olsr->bNeighborChgCausedRemoveFromHigherHop)
		{

			rt_entry* prteTC = QueryRoutingTableAccordingToNodeId(node, olsr->naRecentChangedAddressByTC);


			if (_TEST_TIME_COMPLEXITY && puiLookupCntForAddList)
			{
				uiLCFA++;
			}
							

			if (prteTC != NULL)
			{

				uiOldCostTC = prteTC->rt_metric;

				//this should be true

				topology_last_entry* topo_last = NULL;
				destination_list* topo_dest = NULL;
				if (SYMMETRIC_TOPOLOGY_TABLE)
				{
					topo_last = OlsrLookupLastTopologyTableSYM(node, prteTC->rt_dst);
				}
				else
				{
					topo_last = OlsrLookupLastTopologyTable(node, prteTC->rt_dst);
				}


				if (NULL != topo_last)
				{
					topo_dest = topo_last->topology_list_of_destinations;

					while (topo_dest != NULL)
					{

						Address addrReached = topo_dest->destination_node->topology_destination_dst;



						topo_dest = topo_dest->next;

						BOOL b2HopNeighborCausedConnection = FALSE;

						b2HopNeighborCausedConnection = ConnectivetyCausedBy2HopNeighbor(node, addrReached, olsr->naRecentChangedAddressByTC);
						if (b2HopNeighborCausedConnection)
						{
							continue;
						}


						rt_entry* prte_tmp = QueryRoutingTableAccordingToNodeId(node, addrReached.interfaceAddr.ipv4);

						if (_TEST_TIME_COMPLEXITY && puiLookupCntForAddList)
						{
							uiLCFA++;
						}

						if (prte_tmp != NULL)
						{
							if (prte_tmp->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 == olsr->naRecentChangedAddressByTC)
							{
								//insert_into_tco_node_addr_set(&(destination_list_n_1), addrReached.interfaceAddr.ipv4);

								OlsrDeleteRoutingTable(prte_tmp);

								//prte_tmp->rt_metric = MAX_COST;

								insert_into_tco_node_addr_set(&(olsr->recent_delete_list), addrReached.interfaceAddr.ipv4);
								//insert_into_tco_node_addr_set(&disconnected_list, addrReached.interfaceAddr.ipv4);

							}
						}				


					}
				}


			}


			

			

			//so all the descendants of this old 2Hop neighbor were deleted, and traced in  olsr->recent_delete_list
		}


		if (olsr->recent_add_list == NULL)
		{
			OlsrFillRoutingTableWithSpecificNeighbor(node, olsr->naRecentChangedAddressByTC);
			//see ###$$$ in file Speed-10-6x6-low-TraceRT_SP_ARC_2_tmp15, a special case, may need further study
			
			//it seems it is possible for old un-used 2hop neighbor to exist (seems unreasonable, but do exist)
			list_destination_n = OlsrFillRoutingTableWith2HopNeighborsForSpecificNeighbor(node, olsr->naRecentChangedAddressByTC, &uiLCFA);
		}
		else
		{
			OlsrFillRoutingTableWithSpecificNeighbor(node, olsr->naRecentChangedAddressByTC);
			list_destination_n = OlsrFillRoutingTableWith2HopNeighborsForSpecificNeighbor(node, olsr->naRecentChangedAddressByTC, &uiLCFA);
		}


		if (olsr->bNeighborChgCausedRemoveFromHigherHop) 
		{

			if (olsr->recent_delete_list != NULL)
			{
				tco_node_addr * tmp_recent_delete_list = NULL;

				tco_node_addr * tmp_addr = olsr->recent_delete_list;



				while (tmp_addr != NULL)
				{

					insert_into_tco_node_addr_set(&(tmp_recent_delete_list), tmp_addr->nid);

					tmp_addr = tmp_addr->next;
				}

				//tmp_addr = tmp_recent_delete_list;


				destination_n * list_delete_n = NULL;
				destination_n * list_delete_n_1 = NULL;
				
					
				tco_node_addr * destination_list_n_1 = tmp_recent_delete_list;
				tco_node_addr * destination_list_n = tmp_recent_delete_list;

				while (destination_list_n_1 != NULL)
				{

					destination_list_n_1 = NULL;

					topology_last_entry* topo_last = NULL;
					destination_list* topo_dest = NULL;


					//Peter comment: every loop add group of destination nodes that one hop more from the source node,
					//compare to the group in the previous loop  
					while (destination_list_n != NULL)
					{
						tco_node_addr* tna_tmp = NULL;

						Address addrCurrent;
						addrCurrent.networkType = NETWORK_IPV4;
						addrCurrent.interfaceAddr.ipv4 = destination_list_n->nid;

						//Peter comment: find from the topology table if there is some entry 
						//whose last hop equal the specific dest hop of 2 or more (* since every loop will
						// increase the one more hop count) hop neighbors
						if (SYMMETRIC_TOPOLOGY_TABLE)
						{
							topo_last = OlsrLookupLastTopologyTableSYM(node, addrCurrent);
						}
						else
						{
							topo_last = OlsrLookupLastTopologyTable(node, addrCurrent);
						}


						if (NULL != topo_last)
						{
							topo_dest = topo_last->topology_list_of_destinations;

							while (topo_dest != NULL)
							{

								Address addrReached = topo_dest->destination_node->topology_destination_dst;


								rt_entry* prte_tmp = QueryRoutingTableAccordingToNodeId(node, addrReached.interfaceAddr.ipv4);

								if (_TEST_TIME_COMPLEXITY && puiLookupCntForAddList)
								{
									uiLCFA++;
								}

								if (prte_tmp != NULL)
								{
									if (prte_tmp->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 == destination_list_n->nid)
									{
										insert_into_tco_node_addr_set(&(destination_list_n_1), addrReached.interfaceAddr.ipv4);

										OlsrDeleteRoutingTable(prte_tmp);

										insert_into_tco_node_addr_set(&(olsr->recent_delete_list), addrReached.interfaceAddr.ipv4);

									}
								}				


								topo_dest = topo_dest->next;
							}
						}

						tna_tmp = destination_list_n;
						destination_list_n = destination_list_n->next;
						MEM_free(tna_tmp);
					}

					destination_list_n = destination_list_n_1;

				}
				

			}
			else
			{
				//no further process required, since the following update discovery will deal with all TC's old children

			}

		}


	}
	else
	{
		//only 2hop neighbors are new added

		list_destination_n = OlsrFillRoutingTableWith2HopNeighborsForSpecificNeighbor(node, olsr->naRecentChangedAddressByTC, &uiLCFA);

		
	}

	if (_TEST_TIME_COMPLEXITY && puiLookupCntForAddList != NULL)
	{
		*puiLookupCntForAddList += uiLCFA;
	}	


	return list_destination_n;
}


destination_n* ProcessRoutingTableAccordingToRecentAddListV43(Node* node, UInt32 * puiLookupCntForAddList)
{
	destination_n* list_destination_n = NULL;

	RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;


	UInt32 uiLCFA = 0;


	if (remove_from_tco_node_addr_set(&olsr->recent_add_list, olsr->naRecentChangedAddressByTC))
	{
		//include the route itself and new 2hop neighbors are added

		tco_node_addr * disconnected_list = NULL;

		UInt16 uiOldCostTC = MAX_COST;

		if (olsr->bNeighborChgCausedRemoveFromHigherHop)
		{

		
			//insert_into_tco_node_addr_set(&disconnected_list, olsr->naRecentChangedAddressByTC);

			rt_entry* prteTC = QueryRoutingTableAccordingToNodeId(node, olsr->naRecentChangedAddressByTC);

			if (prteTC != NULL)
			{

				uiOldCostTC = prteTC->rt_metric;

				//this should be true

				topology_last_entry* topo_last = NULL;
				destination_list* topo_dest = NULL;
				if (SYMMETRIC_TOPOLOGY_TABLE)
				{
					topo_last = OlsrLookupLastTopologyTableSYM(node, prteTC->rt_dst);
				}
				else
				{
					topo_last = OlsrLookupLastTopologyTable(node, prteTC->rt_dst);
				}


				if (NULL != topo_last)
				{
					topo_dest = topo_last->topology_list_of_destinations;

					while (topo_dest != NULL)
					{

						Address addrReached = topo_dest->destination_node->topology_destination_dst;



						topo_dest = topo_dest->next;

						BOOL b2HopNeighborCausedConnection = FALSE;

						b2HopNeighborCausedConnection = ConnectivetyCausedBy2HopNeighbor(node, addrReached, olsr->naRecentChangedAddressByTC);
						if (b2HopNeighborCausedConnection)
						{
							continue;
						}


						rt_entry* prte_tmp = QueryRoutingTableAccordingToNodeId(node, addrReached.interfaceAddr.ipv4);

						if (_TEST_TIME_COMPLEXITY && puiLookupCntForAddList)
						{
							uiLCFA++;
						}

						if (prte_tmp != NULL)
						{
							if (prte_tmp->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 == olsr->naRecentChangedAddressByTC)
							{
								//insert_into_tco_node_addr_set(&(destination_list_n_1), addrReached.interfaceAddr.ipv4);

								OlsrDeleteRoutingTable(prte_tmp);

								insert_into_tco_node_addr_set(&(olsr->recent_delete_list), addrReached.interfaceAddr.ipv4);
								insert_into_tco_node_addr_set(&disconnected_list, addrReached.interfaceAddr.ipv4);

							}
						}				


					}
				}


			}



			//if (disconnected_list != NULL)
			{

				/*
				tco_node_addr * tmp_tna = disconnected_list;

				while (tmp_tna != NULL)
				{
					
					rt_entry* prtetmp = QueryRoutingTableAccordingToNodeId(node, tmp_tna->nid);
					
					if (prtetmp)
					{
						//OlsrDeleteRoutingTable(prtetmp);
					}
					

					insert_into_tco_node_addr_set(&(olsr->recent_delete_list), tmp_tna->nid);
					//insert_into_tco_node_addr_set(&disconnected_list, addrReached.interfaceAddr.ipv4);


					tmp_tna = tmp_tna->next;
				}
				*/


				tco_node_addr * destination_list_n_1 = disconnected_list;
				tco_node_addr * destination_list_n = disconnected_list;

				while (destination_list_n_1 != NULL)
				{
					destination_list_n_1 = NULL;

					topology_last_entry* topo_last = NULL;
					destination_list* topo_dest = NULL;


					//Peter comment: every loop add group of destination nodes that one hop more from the source node,
					//compare to the group in the previous loop  
					while (destination_list_n != NULL)
					{
						tco_node_addr* tna_tmp = NULL;

						Address addrCurrent;
						addrCurrent.networkType = NETWORK_IPV4;
						addrCurrent.interfaceAddr.ipv4 = destination_list_n->nid;

						//Peter comment: find from the topology table if there is some entry 
						//whose last hop equal the specific dest hop of 2 or more (* since every loop will
						// increase the one more hop count) hop neighbors
						if (SYMMETRIC_TOPOLOGY_TABLE)
						{
							topo_last = OlsrLookupLastTopologyTableSYM(node, addrCurrent);
						}
						else
						{
							topo_last = OlsrLookupLastTopologyTable(node, addrCurrent);
						}


						if (NULL != topo_last)
						{
							topo_dest = topo_last->topology_list_of_destinations;

							while (topo_dest != NULL)
							{

								Address addrReached = topo_dest->destination_node->topology_destination_dst;


								rt_entry* prte_tmp = QueryRoutingTableAccordingToNodeId(node, addrReached.interfaceAddr.ipv4);

								if (_TEST_TIME_COMPLEXITY && puiLookupCntForAddList)
								{
									uiLCFA++;
								}

								if (prte_tmp != NULL)
								{
									if (prte_tmp->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 == destination_list_n->nid)
									{
										insert_into_tco_node_addr_set(&(destination_list_n_1), addrReached.interfaceAddr.ipv4);

										OlsrDeleteRoutingTable(prte_tmp);

										insert_into_tco_node_addr_set(&(olsr->recent_delete_list), addrReached.interfaceAddr.ipv4);

									}
								}				


								topo_dest = topo_dest->next;
							}
						}

						tna_tmp = destination_list_n;
						destination_list_n = destination_list_n->next;
						MEM_free(tna_tmp);
					}

					destination_list_n = destination_list_n_1;

				}

			}
			//else
			{
				//no further process required, since the following updata discovery will deal with all TC's old children
				
			}
			
			

			//exchange??
			//currently just use the most easy way that form the delete list

			/*
			if (disconnected_list != NULL && prteTC->rt_metric > 2)
			{
				printf("********************************** disconnected_list != NULL, for node %d and olsr->naRecentChangedAddressByTC %d, with prteTC->rt_metric %d, include but not limit to %d \n", node->nodeId, olsr->naRecentChangedAddressByTC, prteTC->rt_metric, disconnected_list->nid);
			}
			*/


			

			//so all the descendants of this old 2Hop neighbor were deleted, and traced in  olsr->recent_delete_list
		}

		if (olsr->recent_add_list == NULL)
		{
			OlsrFillRoutingTableWithSpecificNeighbor(node, olsr->naRecentChangedAddressByTC);
			//see ###$$$ in file Speed-10-6x6-low-TraceRT_SP_ARC_2_tmp15, a special case, may need further study
			
			//it seems it is possible for old un-used 2hop neighbor to exist (seems unreasonable, but do exist)
			list_destination_n = OlsrFillRoutingTableWith2HopNeighborsForSpecificNeighbor(node, olsr->naRecentChangedAddressByTC, &uiLCFA);
		}
		else
		{
			OlsrFillRoutingTableWithSpecificNeighbor(node, olsr->naRecentChangedAddressByTC);
			list_destination_n = OlsrFillRoutingTableWith2HopNeighborsForSpecificNeighbor(node, olsr->naRecentChangedAddressByTC, &uiLCFA);
		}



		if (olsr->bNeighborChgCausedRemoveFromHigherHop)
		{

			if (disconnected_list != NULL)
			{

				/*
				tco_node_addr * tmp_tna = disconnected_list;

				while (tmp_tna != NULL)
				{
					
					rt_entry* prtetmp = QueryRoutingTableAccordingToNodeId(node, tmp_tna->nid);
					
					if (prtetmp)
					{
						//OlsrDeleteRoutingTable(prtetmp);
					}
					

					insert_into_tco_node_addr_set(&(olsr->recent_delete_list), tmp_tna->nid);
					//insert_into_tco_node_addr_set(&disconnected_list, addrReached.interfaceAddr.ipv4);


					tmp_tna = tmp_tna->next;
				}
				*/

				/*
				tco_node_addr * destination_list_n_1 = disconnected_list;
				tco_node_addr * destination_list_n = disconnected_list;

				while (destination_list_n_1 != NULL)
				{
					destination_list_n_1 = NULL;

					topology_last_entry* topo_last = NULL;
					destination_list* topo_dest = NULL;


					//Peter comment: every loop add group of destination nodes that one hop more from the source node,
					//compare to the group in the previous loop  
					while (destination_list_n != NULL)
					{
						tco_node_addr* tna_tmp = NULL;

						Address addrCurrent;
						addrCurrent.networkType = NETWORK_IPV4;
						addrCurrent.interfaceAddr.ipv4 = destination_list_n->nid;

						//Peter comment: find from the topology table if there is some entry 
						//whose last hop equal the specific dest hop of 2 or more (* since every loop will
						// increase the one more hop count) hop neighbors
						if (SYMMETRIC_TOPOLOGY_TABLE)
						{
							topo_last = OlsrLookupLastTopologyTableSYM(node, addrCurrent);
						}
						else
						{
							topo_last = OlsrLookupLastTopologyTable(node, addrCurrent);
						}


						if (NULL != topo_last)
						{
							topo_dest = topo_last->topology_list_of_destinations;

							while (topo_dest != NULL)
							{

								Address addrReached = topo_dest->destination_node->topology_destination_dst;


								rt_entry* prte_tmp = QueryRoutingTableAccordingToNodeId(node, addrReached.interfaceAddr.ipv4);

								if (_TEST_TIME_COMPLEXITY && puiLookupCntForAddList)
								{
									uiLCFA++;
								}

								if (prte_tmp != NULL)
								{
									if (prte_tmp->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 == destination_list_n->nid)
									{
										insert_into_tco_node_addr_set(&(destination_list_n_1), addrReached.interfaceAddr.ipv4);

										OlsrDeleteRoutingTable(prte_tmp);

										insert_into_tco_node_addr_set(&(olsr->recent_delete_list), addrReached.interfaceAddr.ipv4);

									}
								}				


								topo_dest = topo_dest->next;
							}
						}

						tna_tmp = destination_list_n;
						destination_list_n = destination_list_n->next;
						MEM_free(tna_tmp);
					}

					destination_list_n = destination_list_n_1;

				}
				*/

			}
			else
			{
				//no further process required, since the following updata discovery will deal with all TC's old children
				
			}
			

		}

		clear_tco_node_addr_set(&disconnected_list);


	}
	else
	{
		//only 2hop neighbors are new added

		list_destination_n = OlsrFillRoutingTableWith2HopNeighborsForSpecificNeighbor(node, olsr->naRecentChangedAddressByTC, &uiLCFA);

		
	}

	if (_TEST_TIME_COMPLEXITY && puiLookupCntForAddList != NULL)
	{
		*puiLookupCntForAddList += uiLCFA;
	}	


	return list_destination_n;
}


destination_n* ProcessRoutingTableAccordingToRecentAddListV2(Node* node, UInt32 * puiLookupCntForAddList, tco_node_addr ** ptna_set, destination_n** plist_destination_delete)
{

	destination_n* list_destination_n = NULL;

	destination_n* tmp_destination_tail = NULL;

	RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;


	UInt32 uiLCFA = 0;

	tco_node_addr * tco_add_list_tmp = NULL;

	if (ptna_set != NULL)
	{

		tco_add_list_tmp = *ptna_set;
	}
	else
	{

		tco_add_list_tmp = olsr->recent_add_list;
	}
	
	destination_n* tmp_destination = NULL;

	if (plist_destination_delete != NULL)
	{
		tco_add_list_tmp = NULL;
		tmp_destination = *plist_destination_delete;
	}

				
	while (tco_add_list_tmp != NULL || tmp_destination != NULL)
	{

		Int16 iExpectedHopCnt = MAX_COST;
		

		rt_entry* prte = NULL;
		if (tco_add_list_tmp != NULL)
		{
			prte = QueryRoutingTableAccordingToNodeId(node, tco_add_list_tmp->nid);
		}
		else
		{
			prte = tmp_destination->destination;
		}

		
			
		
		if (_TEST_TIME_COMPLEXITY && puiLookupCntForAddList != NULL)
		{
			uiLCFA++;
		}
		

		

		if (prte != NULL)
		{

			iExpectedHopCnt = prte->rt_metric;

			
			//Peter Comment: need to recognize the already existed route entry with cost 1 caused by neigbor table earlier,
			//since it may cause discover according to topology set and find new route for its adjacent node with cost 2,
			//but in fact this adjacent node is not belong to 2hop neigbor set.
			//do it later, during the update discovery
			/*
			if (iExpectedHopCnt == 1)
			{
				tco_add_list_tmp = tco_add_list_tmp->next;
				continue;
			}

			*/

			//pretmp = prte;
		}


		destination_list* topo_dest = NULL;
	
		rt_entry * pretmp = NULL;

		BOOL bSameRoutePrefered = FALSE;

		Address addrTmp;
		addrTmp.networkType = NETWORK_IPV4;


		if (tco_add_list_tmp != NULL)
		{
			addrTmp.interfaceAddr.ipv4 = tco_add_list_tmp->nid;
		}
		else
		{
			addrTmp.interfaceAddr.ipv4 = tmp_destination->destination->rt_entry_infos.rtu_dst.interfaceAddr.ipv4;
		}

		
	
		topology_last_entry * t_last_sym = OlsrLookupLastTopologyTableSYM(node, addrTmp);
		if (t_last_sym != NULL)
		{
			
			topo_dest = t_last_sym->topology_list_of_destinations;

			while (topo_dest != NULL)
			{
				Address addrReached = topo_dest->destination_node->topology_destination_dst;

				rt_entry* prteNearby = QueryRoutingTableAccordingToNodeId(node, addrReached.interfaceAddr.ipv4);
				
				if (_TEST_TIME_COMPLEXITY && puiLookupCntForAddList != NULL)
				{
					uiLCFA++;
				}
				
				if (prteNearby != NULL)
				{

					//Peter Comment: There is a problem that the topology set shows the connectivety while 2-hop neighbor does not show,
					//so current just recognize and skip this case according to the 2hop neighbor
					if (prteNearby->rt_metric == 1)	//addrReached is a neighbor node
					{

						BOOL b2HopNeighborMismatchCausedDisconnect = TRUE;

						b2HopNeighborMismatchCausedDisconnect = DisconnectivetyCausedBy2HopNeighbor(node, addrTmp, prteNearby->rt_entry_infos.rtu_dst.interfaceAddr.ipv4);

						if (b2HopNeighborMismatchCausedDisconnect)
						{
							topo_dest = topo_dest->next;
							continue;
						}
						
					}

					if (iExpectedHopCnt > prteNearby->rt_metric + 1)
					{
												
						iExpectedHopCnt = prteNearby->rt_metric + 1;

						pretmp = prteNearby;
					}
					else //=
					{
						if (g_iToAchieveSameRoute == 1)
						{
							if (iExpectedHopCnt == prteNearby->rt_metric + 1)
							{
								
								if (pretmp != NULL)	//at least there was one prteNearby had this cost
								{
									if (PreferredRouteForNew(prteNearby->rt_entry_infos.rtu_router.interfaceAddr.ipv4, pretmp->rt_entry_infos.rtu_router.interfaceAddr.ipv4))
									{

										pretmp = prteNearby;
										bSameRoutePrefered = TRUE;
									}
								}
								else
								{

									if (prte != NULL)
									{

										if (PreferredRouteForNew(prteNearby->rt_entry_infos.rtu_router.interfaceAddr.ipv4, prte->rt_entry_infos.rtu_router.interfaceAddr.ipv4))
										{
											pretmp = prteNearby;
											bSameRoutePrefered = TRUE;
										}										
									}
								}	
							}
						}
						else
						{

						}
					}
					
				}				

				topo_dest = topo_dest->next;
			}
		}


		BOOL bAlreadyOptimized = FALSE;
		if (iExpectedHopCnt != MAX_COST)
		{

			if (pretmp != NULL)
			{

				if (prte == NULL)
				{

					double dDgrWRT = 0.0;
					double dDtsWRT = 0.0; 


					if (_OLSR_MULTIPATH)
					{
						if (_TEST_TIME_COMPLEXITY)
						{
							dDgrWRT = pretmp->rt_entry_infos.related_neighbor->neighbor_infos.dDegreeWRTNode;
							dDtsWRT = pretmp->rt_entry_infos.related_neighbor->neighbor_infos.dDistanceWRTNode;
						}
						else
						{
							dDgrWRT = pretmp->rt_entry_infos.rtu_DegreeWRTNode;
							dDtsWRT = pretmp->rt_entry_infos.rtu_DistanceWRTNode;
						}
					}

					

					//create the new route entry
					prte =
						OlsrInsertRoutingTablefromTopology(
						node,
						pretmp,
						addrTmp,
						pretmp->rt_dst,
						dDgrWRT, dDtsWRT						
						);

				}
				else
				{
					//the case that this new added topolast entry is already exist wrt to other last_entry,
					//however the existing ones may not have the least cost since it may not consider the connectivety enough,
					//since the knowledge of the whole picture is lack.
					
					//OlsrDeleteRoutingTable(prte);
					
					
					// Lookup best link to get to the router
					
					/*
					link_entry* link = OlsrGetLinktoNeighbor(node, pretmp->rt_router);

					
					if (link == NULL)
					{
						//Assume this branch will never happen
						printf(" No link exists to looked up neighbor, assume this branch will never happen \n");
						//return NULL;

					}
					else
					{
						prte->rt_interface =  RoutingOlsrCheckMyIfaceAddress(
							node,
							link->local_iface_addr);
					}
					*/

					if (iExpectedHopCnt < prte->rt_metric 
						|| g_iToAchieveSameRoute == 1 && bSameRoutePrefered)
					{
						prte->rt_interface = pretmp->rt_interface;

					
						//?????????????????????????????????
						/*
						if (_OLSR_MULTIPATH)
						{

							prte->rt_entry_infos.oa_total_routes_count = pretmp->rt_entry_infos.oa_total_routes_count;
							
							prte->rt_entry_infos.oa_maximum_allowed_cost = pretmp->rt_entry_infos.oa_maximum_allowed_cost;

							prte->rt_entry_infos.oa_dWeightedDirectionDiffer = pretmp->rt_entry_infos.oa_dWeightedDirectionDiffer;
						}
						*/

						/*
						if (iExpectedHopCnt < prte->rt_metric)
						{
							
						}
						*/
						
						prte->rt_entry_infos.rtu_lasthop = pretmp->rt_entry_infos.rtu_dst;
						
						
						prte->rt_router = pretmp->rt_router;
						//prte->rt_metric = (UInt16) (pretmp->rt_metric + 1);
						prte->rt_metric = iExpectedHopCnt;
						


						if (_OLSR_MULTIPATH)
						{

							prte->rt_entry_infos.rtu_DegreeWRTNode = pretmp->rt_entry_infos.rtu_DegreeWRTNode;
							prte->rt_entry_infos.rtu_DistanceWRTNode = pretmp->rt_entry_infos.rtu_DistanceWRTNode;
							prte->rt_entry_infos.related_neighbor = pretmp->rt_entry_infos.related_neighbor;
						}
					}
					else
					{
						bAlreadyOptimized = TRUE;
					}

					
				}

				
			}
			else
			{
				//just use prte, since it must exist and it must has the least cost till now
			}


			//if (!bAlreadyOptimized)
			{
				destination_n* list_destination_tmp;
				list_destination_tmp = (destination_n* )
					MEM_malloc(sizeof(destination_n));

				memset(
					list_destination_tmp,
					0,
					sizeof(destination_n));

				list_destination_tmp->destination = prte;
				
				
				
				//list_destination_tmp->next = list_destination_n;
				//list_destination_n = list_destination_tmp;
			
			
				if (list_destination_n == NULL)
				{
					list_destination_n = list_destination_tmp;
					tmp_destination_tail = list_destination_tmp;
				}
				else
				{

					tmp_destination_tail->next = list_destination_tmp;
					tmp_destination_tail = tmp_destination_tail->next;
				}			
			}			
			
		}
		else
		{
			//do not need to create this new route entry 
			//since it is not connected with the whole picture according to the recent topology table

		}

		if (tco_add_list_tmp != NULL)
		{
			tco_add_list_tmp = tco_add_list_tmp->next;
		}
		else
		{
			tmp_destination = tmp_destination->next;
		}

		
	}


	
	if (_TEST_TIME_COMPLEXITY && puiLookupCntForAddList != NULL)
	{
		*puiLookupCntForAddList = uiLCFA;
	}

	
	return list_destination_n;
}


destination_n* ProcessRoutingTableAccordingToRecentAddList(Node* node, UInt32 * puiLookupCntForAddList)
{

	destination_n* list_destination_n = NULL;

	RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;


	UInt32 uiLCFA = 0;

	tco_node_addr * tco_add_list_tmp = olsr->recent_add_list;			
	while (tco_add_list_tmp != NULL)
	{

		Int16 iExpectedHopCnt = MAX_COST;
		
		rt_entry* prte = QueryRoutingTableAccordingToNodeId(node, tco_add_list_tmp->nid);
		
		if (_TEST_TIME_COMPLEXITY && puiLookupCntForAddList != NULL)
		{
			uiLCFA++;
		}
		

		if (prte != NULL)
		{

			iExpectedHopCnt = prte->rt_metric;

			
			//Peter Comment: need to recognize the already existed route entry with cost 1 caused by neigbor table earlier,
			//since it may cause discover according to topology set and find new route for its adjacent node with cost 2,
			//but in fact this adjacent node is not belong to 2hop neigbor set.
			//do it later, during the update discovery
			/*
			if (iExpectedHopCnt == 1)
			{
				tco_add_list_tmp = tco_add_list_tmp->next;
				continue;
			}

			*/
		}


		destination_list* topo_dest = NULL;
	
		rt_entry * pretmp = NULL;

		Address addrTmp;
		addrTmp.networkType = NETWORK_IPV4;
		addrTmp.interfaceAddr.ipv4 = tco_add_list_tmp->nid;
	
		topology_last_entry * t_last_sym = OlsrLookupLastTopologyTableSYM(node, addrTmp);
		if (t_last_sym != NULL)
		{
			
			topo_dest = t_last_sym->topology_list_of_destinations;

			while (topo_dest != NULL)
			{
				Address addrReached = topo_dest->destination_node->topology_destination_dst;

				rt_entry* prteNearby = QueryRoutingTableAccordingToNodeId(node, addrReached.interfaceAddr.ipv4);
				
				if (_TEST_TIME_COMPLEXITY && puiLookupCntForAddList != NULL)
				{
					uiLCFA++;
				}
				
				if (prteNearby != NULL)
				{


					//Peter Comment: There is a problem that the topology set shows the connectivety while 2-hop neighbor does not show,
					//so current just recognize and skip this case according to the 2hop neighbor
					if (prteNearby->rt_metric == 1)	//addrReached is a neighbor node
					{

						BOOL b2HopNeighborMismatchCausedDisconnect = TRUE;

						neighbor_2_entry *two_hop_neighbor = NULL;

						two_hop_neighbor = OlsrLookup2HopNeighborTable(node, addrTmp);
						
						if (two_hop_neighbor)
						{

							//DebugBreak();

							neighbor_list_entry* list_1 = NULL;
							list_1 = two_hop_neighbor->neighbor_2_nblist;

							while (list_1 != NULL)
							{
								/*
								IO_ConvertIpAddressToString(
									&list_1->neighbor->neighbor_main_addr,
									addrString);

								if (g_iChaseRouteTable == 1)
								{
									sprintf(g_szTextRT, "%s%s ", g_szTextRT, addrString);
								}
								else
								{
									printf("%s ", addrString);
								}
								*/
								if (Address_IsSameAddress(&list_1->neighbor->neighbor_main_addr, &addrReached))
								{
									b2HopNeighborMismatchCausedDisconnect = FALSE;
									break;
								}																

								list_1 = list_1->neighbor_next;
							}

						}
						else
						{
							//b2HopNeighborMismatchCausedDisconnect = TRUE;
						}

						if (b2HopNeighborMismatchCausedDisconnect)
						{
							topo_dest = topo_dest->next;
							continue;
						}
						
					}

					if (iExpectedHopCnt > prteNearby->rt_metric + 1)
					{
						
						
						iExpectedHopCnt = prteNearby->rt_metric + 1;

						pretmp = prteNearby;
					}
					else
					{
					}
					
				}				

				topo_dest = topo_dest->next;
			}
		}


		if (iExpectedHopCnt != MAX_COST)
		{

			if (pretmp != NULL)
			{

				if (prte == NULL)
				{

					double dDgrWRT = 0.0;
					double dDtsWRT = 0.0; 



					if (_OLSR_MULTIPATH)
					{
						if (_TEST_TIME_COMPLEXITY)
						{
							dDgrWRT = pretmp->rt_entry_infos.related_neighbor->neighbor_infos.dDegreeWRTNode;
							dDtsWRT = pretmp->rt_entry_infos.related_neighbor->neighbor_infos.dDistanceWRTNode;
						}
						else
						{
							dDgrWRT = pretmp->rt_entry_infos.rtu_DegreeWRTNode;
							dDtsWRT = pretmp->rt_entry_infos.rtu_DistanceWRTNode;
						}
					}


					

					//create the new route entry
					prte =
						OlsrInsertRoutingTablefromTopology(
						node,
						pretmp,
						addrTmp,
						pretmp->rt_dst,
						dDgrWRT, dDtsWRT						
						);

				}
				else
				{
					//the case that this new added topolast entry is already exist wrt to other last_entry,
					//however the existing ones may not have the least cost since it may not consider the connectivety enough,
					//since the knowledge of the whole picture is lack.
					
					//OlsrDeleteRoutingTable(prte);
					
					
					// Lookup best link to get to the router
					
					/*
					link_entry* link = OlsrGetLinktoNeighbor(node, pretmp->rt_router);

					
					if (link == NULL)
					{
						//Assume this branch will never happen
						printf(" No link exists to looked up neighbor, assume this branch will never happen \n");
						//return NULL;

					}
					else
					{
						prte->rt_interface =  RoutingOlsrCheckMyIfaceAddress(
							node,
							link->local_iface_addr);
					}
					*/

					prte->rt_interface = pretmp->rt_interface;

					
					//?????????????????????????????????
					/*
					if (_OLSR_MULTIPATH)
					{

						prte->rt_entry_infos.oa_total_routes_count = pretmp->rt_entry_infos.oa_total_routes_count;
						
						prte->rt_entry_infos.oa_maximum_allowed_cost = pretmp->rt_entry_infos.oa_maximum_allowed_cost;

						prte->rt_entry_infos.oa_dWeightedDirectionDiffer = pretmp->rt_entry_infos.oa_dWeightedDirectionDiffer;
					}
					*/

					prte->rt_entry_infos.rtu_lasthop = pretmp->rt_dst;
					prte->rt_router = pretmp->rt_router;
					prte->rt_metric = (UInt16) (pretmp->rt_metric + 1);
					

					prte->rt_entry_infos.rtu_DegreeWRTNode = pretmp->rt_entry_infos.rtu_DegreeWRTNode;
					prte->rt_entry_infos.rtu_DistanceWRTNode = pretmp->rt_entry_infos.rtu_DistanceWRTNode;
					prte->rt_entry_infos.related_neighbor = pretmp->rt_entry_infos.related_neighbor;
				}

				
			}
			else
			{
				//just use prte, since it must exist and it must has the least cost till now
			}

			
			destination_n* list_destination_tmp;
			list_destination_tmp = (destination_n* )
				MEM_malloc(sizeof(destination_n));

			memset(
				list_destination_tmp,
				0,
				sizeof(destination_n));

			list_destination_tmp->destination = prte;
			list_destination_tmp->next = list_destination_n;
			list_destination_n = list_destination_tmp;
		}
		else
		{
			//do not need to create this new route entry 
			//since it is not connected with the whole picture according to the recent topology table

		}


		tco_add_list_tmp = tco_add_list_tmp->next;
	}


	/*
	tco_node_addr * tco_delete_list_tmp = olsr->recent_delete_list;
	while (tco_delete_list_tmp != NULL)
	{

		//currently just skip this case

		tco_delete_list_tmp = tco_delete_list_tmp->next;

	}
	*/
	if (_TEST_TIME_COMPLEXITY && puiLookupCntForAddList != NULL)
	{
		*puiLookupCntForAddList = uiLCFA;
	}

	
	return list_destination_n;
}


destination_n* ProcessRoutingTableAccordingToRecentAddListMP(Node* node, UInt32 * puiLookupCntForAddList)
{

	destination_n* list_destination_n = NULL;

	RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;


	UInt32 uiLCFA = 0;

	tco_node_addr * tco_add_list_tmp = olsr->recent_add_list;			
	while (tco_add_list_tmp != NULL)
	{

		//Int16 iExpectedHopCnt = MAX_COST;
		
		rthash * rhRetrieve = NULL;
		rt_entry* prte = QueryRoutingTableAccordingToNodeId(node, tco_add_list_tmp->nid, NULL, &rhRetrieve);
		
		if (_TEST_TIME_COMPLEXITY && puiLookupCntForAddList != NULL)
		{
			uiLCFA++;
		}
		
		if (prte != NULL)
		{

			for ( ; prte != (rt_entry* ) rhRetrieve; prte = prte->rt_back)
			{

				Int16 iExpectedHopCnt = MAX_COST;

				if (prte != NULL)
				{

					iExpectedHopCnt = prte->rt_metric;
				}


				destination_list* topo_dest = NULL;

				rt_entry * pretmp = NULL;

				Address addrTmp;
				addrTmp.networkType = NETWORK_IPV4;
				addrTmp.interfaceAddr.ipv4 = tco_add_list_tmp->nid;

				topology_last_entry * t_last_sym = OlsrLookupLastTopologyTableSYM(node, addrTmp);
				if (t_last_sym != NULL)
				{

					topo_dest = t_last_sym->topology_list_of_destinations;

					while (topo_dest != NULL)
					{
						Address addrReached = topo_dest->destination_node->topology_destination_dst;

						NodeAddress naRoute = prte->rt_entry_infos.rtu_router.interfaceAddr.ipv4;
						rt_entry* prteNearby = QueryRoutingTableAccordingToNodeId(node, addrReached.interfaceAddr.ipv4, &naRoute, NULL);

						if (_TEST_TIME_COMPLEXITY && puiLookupCntForAddList != NULL)
						{
							uiLCFA++;
						}

						if (prteNearby != NULL)
						{

							if (iExpectedHopCnt > prteNearby->rt_metric + 1)
							{

								iExpectedHopCnt = prteNearby->rt_metric + 1;

								pretmp = prteNearby;
							}
							else
							{
							}

						}				

						topo_dest = topo_dest->next;
					}
				
				
				}

			
				
				if (iExpectedHopCnt != MAX_COST)
				{

					if (pretmp != NULL)
					{

						
						{
							//the case that this new added topolast entry is already exist wrt to other last_entry,
							//however the existing ones may not have the least cost since it may not consider the connectivety enough,
							//since the knowledge of the whole picture is lack.
							
							//OlsrDeleteRoutingTable(prte);
							
							
							// Lookup best link to get to the router
							
							

							prte->rt_interface = pretmp->rt_interface;

							
							//?????????????????????????????????
							/*
							if (_OLSR_MULTIPATH)
							{

								prte->rt_entry_infos.oa_total_routes_count = pretmp->rt_entry_infos.oa_total_routes_count;
								
								prte->rt_entry_infos.oa_maximum_allowed_cost = pretmp->rt_entry_infos.oa_maximum_allowed_cost;

								prte->rt_entry_infos.oa_dWeightedDirectionDiffer = pretmp->rt_entry_infos.oa_dWeightedDirectionDiffer;
							}
							*/

							prte->rt_entry_infos.rtu_lasthop = pretmp->rt_dst;
							prte->rt_router = pretmp->rt_router;
							prte->rt_metric = (UInt16) (pretmp->rt_metric + 1);
							

							prte->rt_entry_infos.rtu_DegreeWRTNode = pretmp->rt_entry_infos.rtu_DegreeWRTNode;
							prte->rt_entry_infos.rtu_DistanceWRTNode = pretmp->rt_entry_infos.rtu_DistanceWRTNode;
							prte->rt_entry_infos.related_neighbor = pretmp->rt_entry_infos.related_neighbor;
						}

						
					}
					else
					{
						//just use prte, since it must exist and it must has the least cost till now
					}

					/*
					destination_n* list_destination_tmp;
					list_destination_tmp = (destination_n* )
						MEM_malloc(sizeof(destination_n));

					memset(
						list_destination_tmp,
						0,
						sizeof(destination_n));

					list_destination_tmp->destination = prte;
					list_destination_tmp->next = list_destination_n;
					list_destination_n = list_destination_tmp;
					*/
				}
				else
				{
					//do not need to create this new route entry 
					//since it is not connected with the whole picture according to the recent topology table

				}


			}

		}
		else
		{
			
			Int16 iExpectedHopCnt = MAX_COST;

			destination_list* topo_dest = NULL;

			rt_entry * pretmp = NULL;

			Address addrTmp;
			addrTmp.networkType = NETWORK_IPV4;
			addrTmp.interfaceAddr.ipv4 = tco_add_list_tmp->nid;

			topology_last_entry * t_last_sym = OlsrLookupLastTopologyTableSYM(node, addrTmp);
			if (t_last_sym != NULL)
			{

				topo_dest = t_last_sym->topology_list_of_destinations;

				while (topo_dest != NULL)
				{
					Address addrReached = topo_dest->destination_node->topology_destination_dst;

					//NodeAddress naRoute = prte->rt_entry_infos.rtu_router.interfaceAddr.ipv4;
					rthash * rhRetrieve = NULL;
								
					rt_entry* prteNearby = QueryRoutingTableAccordingToNodeId(node, addrReached.interfaceAddr.ipv4, NULL, &rhRetrieve);

					if (_TEST_TIME_COMPLEXITY && puiLookupCntForAddList != NULL)
					{
						uiLCFA++;
					}

					if (prteNearby != NULL)
					{

						for ( ; prteNearby != (rt_entry* ) rhRetrieve; prteNearby = prteNearby->rt_back)
						{

							NodeAddress naRoute = prteNearby->rt_entry_infos.rtu_router.interfaceAddr.ipv4;
							rt_entry* prte2 = QueryRoutingTableAccordingToNodeId(node, tco_add_list_tmp->nid, &naRoute, NULL);

							if (_TEST_TIME_COMPLEXITY && puiLookupCntForAddList != NULL)
							{
								uiLCFA++;
							}

							if (prte2 != NULL)
							{

								if (prte2->rt_metric > prteNearby->rt_metric + 1)
								{

									
									//update
									
									{

										{

											
											{
												

												prte2->rt_interface = prteNearby->rt_interface;

												
												//?????????????????????????????????
												/*
												if (_OLSR_MULTIPATH)
												{

													prte2->rt_entry_infos.oa_total_routes_count = prteNearby->rt_entry_infos.oa_total_routes_count;
													
													prte2->rt_entry_infos.oa_maximum_allowed_cost = prteNearby->rt_entry_infos.oa_maximum_allowed_cost;

													prte2->rt_entry_infos.oa_dWeightedDirectionDiffer = prteNearby->rt_entry_infos.oa_dWeightedDirectionDiffer;
												}
												*/

												prte2->rt_entry_infos.rtu_lasthop = prteNearby->rt_dst;
												prte2->rt_router = prteNearby->rt_router;
												prte2->rt_metric = (UInt16) (prteNearby->rt_metric + 1);
												

												prte2->rt_entry_infos.rtu_DegreeWRTNode = prteNearby->rt_entry_infos.rtu_DegreeWRTNode;
												prte2->rt_entry_infos.rtu_DistanceWRTNode = prteNearby->rt_entry_infos.rtu_DistanceWRTNode;
												prte2->rt_entry_infos.related_neighbor = prteNearby->rt_entry_infos.related_neighbor;
											}

											
										}
										//else
										{
											//just use prte, since it must exist and it must has the least cost till now
										}

										/*
										destination_n* list_destination_tmp;
										list_destination_tmp = (destination_n* )
											MEM_malloc(sizeof(destination_n));

										memset(
											list_destination_tmp,
											0,
											sizeof(destination_n));

										list_destination_tmp->destination = prte;
										list_destination_tmp->next = list_destination_n;
										list_destination_n = list_destination_tmp;
										*/
									}
									//else
									{
										//do not need to create this new route entry 
										//since it is not connected with the whole picture according to the recent topology table

									}
								}
								else
								{
									//skip
								}
							
							}
							else
							{
							
								double dDgrWRT = 0.0;
								double dDtsWRT = 0.0; 

								if (_TEST_TIME_COMPLEXITY)
								{
									dDgrWRT = prteNearby->rt_entry_infos.related_neighbor->neighbor_infos.dDegreeWRTNode;
									dDtsWRT = prteNearby->rt_entry_infos.related_neighbor->neighbor_infos.dDistanceWRTNode;
								}
								else
								{
									dDgrWRT = prteNearby->rt_entry_infos.rtu_DegreeWRTNode;
									dDtsWRT = prteNearby->rt_entry_infos.rtu_DistanceWRTNode;
								}


								RouteEntryType ret = OlsrAdvancedLookupRoutingTable(node, addrTmp, 
									prteNearby->rt_router, 
									(UInt16)(prteNearby->rt_metric + 1), dDgrWRT, 
									_OLSR_TEMP_ROUTES_LIMIT, prteNearby->rt_dst);


								if (ret != NOT_ALLOWED)
								{

									//create the new route entry
									prte2 =
										OlsrInsertRoutingTablefromTopology(
										node,
										prteNearby,
										addrTmp,
										prteNearby->rt_dst,
										dDgrWRT, dDtsWRT						
										);
								}

								


							}
							

						
						}


						

					}				

					topo_dest = topo_dest->next;
				}
			
			
			}

		
		}




		rhRetrieve = NULL;
		prte = NULL;
		
		prte = QueryRoutingTableAccordingToNodeId(node, tco_add_list_tmp->nid, NULL, &rhRetrieve);

		if (_TEST_TIME_COMPLEXITY && puiLookupCntForAddList != NULL)
		{
			uiLCFA++;
		}

		if (prte != NULL)
		{

			for ( ; prte != (rt_entry* ) rhRetrieve; prte = prte->rt_back)
			{  

				destination_n* list_destination_tmp;
				list_destination_tmp = (destination_n* )
					MEM_malloc(sizeof(destination_n));

				memset(
					list_destination_tmp,
					0,
					sizeof(destination_n));

				list_destination_tmp->destination = prte;
				list_destination_tmp->next = list_destination_n;
				list_destination_n = list_destination_tmp;

			}
		
		}




		tco_add_list_tmp = tco_add_list_tmp->next;
	}


	/*
	tco_node_addr * tco_delete_list_tmp = olsr->recent_delete_list;
	while (tco_delete_list_tmp != NULL)
	{

		//currently just skip this case

		tco_delete_list_tmp = tco_delete_list_tmp->next;

	}
	*/
	if (_TEST_TIME_COMPLEXITY && puiLookupCntForAddList != NULL)
	{
		*puiLookupCntForAddList = uiLCFA;
	}

	
	return list_destination_n;
}


void ProcessRoutingTableAccordingToSpecificRoute(Node* node, NodeAddress naRoute, destination_n** plist_destination_delete)
{

	destination_n* list_destination_n = NULL;

	RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

	rt_entry* destination;
	rt_entry* destination_tmp;
	rthash* routing_hash;

	unsigned char index;

	for (index = 0; index < HASHSIZE; index++)
	{

		routing_hash = &olsr->routingtable[index];

		destination = routing_hash->rt_forw;
		while (destination != (rt_entry *) routing_hash)
		{

			destination_tmp = destination;
			destination = destination->rt_forw;

			// deletes each routing entry from the table

			if (destination_tmp->rt_entry_infos.rtu_router.interfaceAddr.ipv4 == naRoute)
			{

				BOOL bAvoidMaxFor2HopExchangeYet = FALSE;
				
				if (g_iAccumulativeRouteCalculation == 2 || g_iAccumulativeRouteCalculation == 1)
				{
					if (destination_tmp->rt_entry_infos.rtu_metric == 2 || destination_tmp->rt_entry_infos.rtu_dst.interfaceAddr.ipv4 == naRoute)
					{


						//BOOL b2HopReplaceFound = FALSE;
						neighbor_2_entry* two_hop_neighbor = OlsrLookup2HopNeighborTable(node, destination_tmp->rt_entry_infos.rtu_dst);

						if (two_hop_neighbor != NULL)
						{

							neighbor_list_entry* list_1 = NULL;
							list_1 = two_hop_neighbor->neighbor_2_nblist;

							neighbor_entry * pneTmp = NULL;

							while (list_1 != NULL)
							{

								if (g_iToAchieveSameRoute != 1)
								{

									if (list_1->neighbor->neighbor_status == SYM)
									{
										pneTmp = list_1->neighbor;
										break;
									}								
								}
								else
								{

									if (list_1->neighbor->neighbor_status == SYM)
									{
										if (pneTmp == NULL)
										{
											pneTmp = list_1->neighbor;
										}
										else
										{
											if (PreferredRouteForNew(list_1->neighbor->neighbor_main_addr.interfaceAddr.ipv4, pneTmp->neighbor_main_addr.interfaceAddr.ipv4))
											{
												pneTmp = list_1->neighbor;
											}
										}
									}

								}

								list_1 = list_1->neighbor_next;
							}

							if (pneTmp != NULL)
							{
								link_entry* link = OlsrGetBestLinktoNeighbor(
									node,
									pneTmp->neighbor_main_addr);

								if (link)
								{


									//rt_entry* new_route_entry = NULL;


									{
										//new_route_entry = destination_tmp;
									}



									destination_tmp->rt_router =
										link->neighbor_iface_addr;

									destination_tmp->rt_entry_infos.rtu_lasthop = link->neighbor_iface_addr;


									if (_OLSR_MULTIPATH)
									{
										if (_TEST_TIME_COMPLEXITY)
										{
											destination_tmp->rt_entry_infos.related_neighbor = pneTmp;					

										}
										else
										{
											//new_route_entry->rt_entry_infos.rtu_DegreeWRTNode = dRWON;

											//new_route_entry->rt_entry_infos.rtu_DistanceWRTNode = dDistance;

										}
									}


									// The next router is the neighbor itself
									destination_tmp->rt_metric = 2;

									destination_tmp->rt_interface =
										RoutingOlsrCheckMyIfaceAddress(
										node,
										link->local_iface_addr);

								}
								else
								{
									//should never happen
								}


								if (g_iToAchieveSameRoute == 1)
								{
									//should goes to the delete list, 
									//since its adjacent nodes may not be deleted as well,
									//so the change of route has to be updated to them by update&discovery

									bAvoidMaxFor2HopExchangeYet = TRUE;
								}
								else
								{
									continue;
								}							
							}
						}
					}
				}
				else //g_iAccumulativeRouteCalculation == 0
				{
					//never happen
				}

				insert_into_tco_node_addr_set(&olsr->recent_add_list, destination_tmp->rt_entry_infos.rtu_dst.interfaceAddr.ipv4); 

				if (plist_destination_delete != NULL)	//g_iAccumulativeRouteCalculation == 2
				{

					destination_n* list_destination_tmp;
					list_destination_tmp = (destination_n*)
						MEM_malloc(sizeof(destination_n));

					memset(
						list_destination_tmp,
						0,
						sizeof(destination_n));

					if (bAvoidMaxFor2HopExchangeYet && g_iToAchieveSameRoute == 1)
					{

					}
					else
					{
						destination_tmp->rt_entry_infos.rtu_metric = MAX_COST;
					}
					


					list_destination_tmp->destination = destination_tmp;

					list_destination_tmp->next = *plist_destination_delete;
					*plist_destination_delete = list_destination_tmp;
				}
				else	////g_iAccumulativeRouteCalculation == 1
				{
					if (bAvoidMaxFor2HopExchangeYet && g_iToAchieveSameRoute == 1)
					{

					}
					else
					{
						OlsrDeleteRoutingTable(destination_tmp);
					}					
					
				}
			}			
		}
	}

	//return list_destination_n;
}

destination_n* ProcessRoutingTableAccordingToConfidentCost(Node* node, UInt16 uiConfidentCost)
{

	destination_n* list_destination_n = NULL;

	RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

	rt_entry* destination;
	rt_entry* destination_tmp;
	rthash* routing_hash;

	unsigned char index;

	for (index = 0; index < HASHSIZE; index++)
	{
		
		routing_hash = &olsr->routingtable[index];
				
		destination = routing_hash->rt_forw;
		while (destination != (rt_entry *) routing_hash)
		{
		
			destination_tmp = destination;
			destination = destination->rt_forw;

			// deletes each routing entry from the table

			if (destination_tmp->rt_entry_infos.rtu_metric > uiConfidentCost)
			{
				OlsrDeleteRoutingTable(destination_tmp);
			}
			else if (destination_tmp->rt_entry_infos.rtu_metric == uiConfidentCost)
			{

				//try to add generate the work set here	
			
				destination_n* list_destination_tmp;
				list_destination_tmp = (destination_n* )
					MEM_malloc(sizeof(destination_n));

				memset(
					list_destination_tmp,
					0,
					sizeof(destination_n));

				list_destination_tmp->destination = destination_tmp;
				list_destination_tmp->next = list_destination_n;
				list_destination_n = list_destination_tmp;
			
			}
			else	// <
			{
				
				
				//assume that the route entries are sorted by cost,
				//because of the principle that later added entry will have larger cost.
				
				
				//??????????
				//Since different nodes may be assigned into same hase  
				//break;
			}
		}
	}

	return list_destination_n;
}

BOOL CheckCachedRoute(Node *node, Message *msg, int * iInterface, NodeAddress * naNextHop)
{


	RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

	RouteCacheItem * pRCI = &(olsr->rci);

	if (pRCI->bIsUseful)
	{
		

		*iInterface = pRCI->interfaceIndexCache;

		*naNextHop = pRCI->nextHopAddressCache;


		msg->dDegreeDiffForThirdPartyNode = pRCI->dDegreeDiffForThirdPartyNodeCache;

		msg->TestNorthSouthNodeId = pRCI->TestNorthSouthNodeIdCache;

		msg->dExpectedDistanceInOneHop = pRCI->dExpectedDistanceInOneHopCache;

		msg->dDeltaDegree = pRCI->dDeltaDegreeCache;

			
		msg->numberOfLeastHops = pRCI->numberOfLeastHopsCache;

		msg->numberOfExperiencedHops = pRCI->numberOfExperiencedHopsCache;

		msg->numberOfTotalHops = pRCI->numberOfTotalHopsCache;

		msg->dEstimatedCurrentDistanceInOneHop = pRCI->dEstimatedCurrentDistanceInOneHopCache;

		msg->dEstimatedCurrentWidthInOneHop = pRCI->dEstimatedCurrentWidthInOneHopCache;

		msg->dRecentRelativeDegree = pRCI->dRecentRelativeDegreeCache;

		msg->dRecentRelativeDistance = pRCI->dRecentRelativeDistanceCache;
	
	}
	else
	{
		return FALSE;
	}
	
	return TRUE;
}

void UpdateRoouteCache(Node *node, Message *msg, int iInterface, NodeAddress naNextHop)
{

	RoutingOlsr* olsr = (RoutingOlsr* ) node->appData.olsr;

	RouteCacheItem * pRCI = &(olsr->rci);


	pRCI->interfaceIndexCache = iInterface;

	pRCI->nextHopAddressCache = naNextHop;


	pRCI->dDegreeDiffForThirdPartyNodeCache = msg->dDegreeDiffForThirdPartyNode;

	pRCI->TestNorthSouthNodeIdCache = msg->TestNorthSouthNodeId;
		
	pRCI->dExpectedDistanceInOneHopCache = msg->dExpectedDistanceInOneHop;

	pRCI->dDeltaDegreeCache = msg->dDeltaDegree;

	pRCI->numberOfLeastHopsCache = msg->numberOfLeastHops;

	pRCI->numberOfExperiencedHopsCache = msg->numberOfExperiencedHops;

	pRCI->numberOfTotalHopsCache = msg->numberOfTotalHops;

	pRCI->dEstimatedCurrentDistanceInOneHopCache = msg->dEstimatedCurrentDistanceInOneHop;

	pRCI->dEstimatedCurrentWidthInOneHopCache = msg->dEstimatedCurrentWidthInOneHop;

	pRCI->dRecentRelativeDegreeCache = msg->dRecentRelativeDegree;

	pRCI->dRecentRelativeDistanceCache = msg->dRecentRelativeDistance;

	
	pRCI->bIsUseful = TRUE;

	return;
}


void RelatedTimeTrace(Node *node, char * pszDesc)
{


	/*
	char timeStr[MAX_STRING_LENGTH];

	TIME_PrintClockInSecond(getSimTime(node), timeStr, node);

	double dSimTime = atof(timeStr);
	*/

	
	/*
	if (dSimTime > 19 && dSimTime < 25)
	{
		char timeStr2[MAX_STRING_LENGTH];

		TIME_PrintClockInSecond(EXTERNAL_QueryRealTime(), timeStr2, node);
		double dRealTime = atof(timeStr2);

		
		printf("%s for node no. %d at Sim Time %f, and Real Time %f \n", pszDesc, node->nodeId, dSimTime, dRealTime);

	}
	*/

	
}


void CompareRTPre(Node *node)
{

	//CmpBreakPoint(node);

	

	RoutingOlsr* olsr = (RoutingOlsr *) node->appData.olsr;

	RelatedTimeTrace(node, "CompareRTPre start");
	



	memset(olsr->pszOrigRT, 0, RT_SIZE * sizeof(char));
	OlsrPrintRoutingTable(olsr->routingtable, olsr->pszOrigRT);

	if (g_iSpecailDebug == 1)
	{
		printf("\n\n++++++++++++++++++++++++++++++ Special Debug Section Start +++++++++++++++++++++++\n");



		SpecialDebug(node, DEBUG_NODE_ID, DEBUG_ENTRY_ID);

	}


	RelatedTimeTrace(node, "CompareRTPre end");



}

//pszMiddleRT: for the state between add and delete when both exists
void CompareRTMiddle(Node *node)
{


	RoutingOlsr* olsr = (RoutingOlsr *) node->appData.olsr;

	memset(olsr->pszMiddleRT, 0, RT_SIZE * sizeof(char));
	OlsrPrintRoutingTable(olsr->routingtable, olsr->pszMiddleRT);

	if (g_iSpecailDebug == 1)
	{
		printf("\n\n++++++++++++++++++++++++++++++ Special Debug Section Middle +++++++++++++++++++++++\n");


		SpecialDebug(node, DEBUG_NODE_ID, DEBUG_ENTRY_ID);

	}

}

void CompareRT(Node *node, int iRTAddOrDelete)
{

	
	char szTextRT_w[RT_SIZE_THIN];

	char szTextRT_wo[RT_SIZE_THIN];


	RoutingOlsr* olsr = (RoutingOlsr *) node->appData.olsr;


	RelatedTimeTrace(node, "CompareRT start");


	memset(szTextRT_w, 0, RT_SIZE_THIN * sizeof(char));	
	OlsrPrintRoutingTable(olsr->routingtable, szTextRT_w, FALSE);


	memset(olsr->pszRTWithARC, 0, RT_SIZE * sizeof(char));
	OlsrPrintRoutingTable(olsr->routingtable, olsr->pszRTWithARC);


	if (g_iSpecailDebug == 1)
	{

		printf("\n-------------------------------- Special Debug After ARC ----------------------------\n");

		SpecialDebug(node, DEBUG_NODE_ID, DEBUG_ENTRY_ID);

		

	}

	

	//execute the classic RC for compare	
	OlsrCalculateRoutingTableForCompare(node);


	if (g_iSpecailDebug == 1)
	{

		printf("\n-------------------------------- Special Debug After classic RC ----------------------------\n");

		SpecialDebug(node, DEBUG_NODE_ID, DEBUG_ENTRY_ID);

		printf("\n-------------------------------- Special Debug Section End ----------------------------\n\n");

	}


	memset(szTextRT_wo, 0, RT_SIZE_THIN * sizeof(char));
	OlsrPrintRoutingTable(olsr->mirror_table, szTextRT_wo, FALSE);


	int iRet = strcmp(szTextRT_w, szTextRT_wo);

	if (iRet != 0)
	{

		memset(olsr->pszRTWithoutARC, 0, RT_SIZE * sizeof(char));
		OlsrPrintRoutingTable(olsr->mirror_table, olsr->pszRTWithoutARC);


		//start to print out

		printf("********************** There is difference between resulted route tables ********************** \n");


		printf(olsr->pszInfo);


		printf("\nOrig RT: \n");

		printf(olsr->pszOrigRT);
		

		//g_iChaseRouteTable = 1;
		
		memset(olsr->pszOtherTables, 0, RT_SIZE * sizeof(char));
		OlsrPrintNeighborTable(node);

		printf("%s \n", olsr->pszOtherTables);

		

		memset(olsr->pszOtherTables, 0, RT_SIZE * sizeof(char));
		OlsrPrint2HopNeighborTable(node);

		printf("%s \n", olsr->pszOtherTables);


		memset(olsr->pszOtherTables, 0, RT_SIZE * sizeof(char));
		OlsrPrintTopologyTableSYM(node);

		printf("%s \n", olsr->pszOtherTables);


		//g_iChaseRouteTable = 0;

		//sprintf(szTextRT, "%s%s", szTextRT, g_szTextRT);

		if (iRTAddOrDelete == 3)
		{
			printf("\nMiddle RT: \n");

			printf(olsr->pszMiddleRT);

			printf("\n\n");
		}


		printf("RT with ARC: \n");

		printf(olsr->pszRTWithARC);

		printf("\n\n");


		printf("RT without ARC: \n");

		printf(olsr->pszRTWithoutARC);

		printf("\n\n\n\n");
	}

	RelatedTimeTrace(node, "CompareRT end");


}

void SpecialDebug(Node *node, NodeAddress naId, NodeAddress naEntryId)
{
		
	if (node->nodeId == naId)
	{
		rt_entry* prt_tmp = QueryRoutingTableAccordingToNodeId(node, naEntryId);

		if (prt_tmp != NULL)
		{
			char szTmp[INFO_SIZE];
			memset(szTmp, 0, INFO_SIZE * sizeof(char));

			PrintRoutingTableForAEntry(prt_tmp, szTmp);

			printf(szTmp);
		}
	}
		
}


BOOL PreferredRouteForNew(NodeAddress naNew, NodeAddress naCurrent)
{

	BOOL bNewPreferred = FALSE;


	if (naCurrent == naNew)
	{
		//nothing happen
	}
	else
	{

		UInt16 uiNew = naNew % HASHSIZE;
		UInt16 uiCurrent = naCurrent % HASHSIZE;


		if (uiNew == uiCurrent)
		{
			if (naNew < naCurrent)
			{
				bNewPreferred = TRUE;
			}
		}
		else
		{

			if (uiNew < uiCurrent)
			{

				bNewPreferred = TRUE;
			}
		}

	}

	return bNewPreferred;
	
}


void DeleteListProgress(Node* node, e2_s* pe2_n, e2_s* pe2_n_1, tco_node_addr ** ptna_delete_set, destination_n** plist_destination_delete)
{


	if (pe2_n->list_delete)
	{

		while (pe2_n->list_delete != NULL)
		{
			//DebugBreak();
			destination_n* destination_n_1 = NULL;
			destination_list* topo_dest = NULL;
			
			if (pe2_n->list_delete->bChildrenDetermined)
			{
				destination_n * dst_child = pe2_n->list_delete->children;
				while (dst_child != NULL)
				{

					//Address addrReached = dst_child->destination->rt_entry_infos.rtu_dst;							

					//UInt32 uiInnerExchangeLUCnt = 0;
					rt_entry* prteNearby = dst_child->destination;
					if (prteNearby != NULL)
					{

						if (prteNearby->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 == pe2_n->list_delete->destination->rt_entry_infos.rtu_dst.interfaceAddr.ipv4)
						{


							prteNearby->rt_metric = MAX_COST;

							destination_n* list_destination_tmp;
							list_destination_tmp = (destination_n* )
								MEM_malloc(sizeof(destination_n));

							memset(
								list_destination_tmp,
								0,
								sizeof(destination_n));

							list_destination_tmp->destination = prteNearby;


							{
								list_destination_tmp->children = dst_child->children;
								list_destination_tmp->bChildrenDetermined = dst_child->bChildrenDetermined;

								dst_child->children = NULL;
							}



							list_destination_tmp->next = pe2_n_1->list_delete;
							pe2_n_1->list_delete = list_destination_tmp;



						}
						

					}

					
					dst_child = dst_child->next;
				}

				insert_into_tco_node_addr_set(ptna_delete_set, pe2_n->list_delete->destination->rt_entry_infos.rtu_dst.interfaceAddr.ipv4);
			}
			else
			{
				topology_last_entry* topo_last = OlsrLookupLastTopologyTableSYM(node, pe2_n->list_delete->destination->rt_dst);

				/*
				if (_TEST_TIME_COMPLEXITY && puiLookupCntForAddList)
				{

					uiLCFA ++;

				}
				*/

				BOOL bInsideNode = TRUE;

				if (NULL != topo_last)
				{
					topo_dest = topo_last->topology_list_of_destinations;

					while (topo_dest != NULL)
					{

						Address addrReached = topo_dest->destination_node->topology_destination_dst;


						UInt32 uiInnerExchangeLUCnt = 0;

						rt_entry* prteNearby = QueryRoutingTableAccordingToNodeId(node, addrReached.interfaceAddr.ipv4);
						if (prteNearby != NULL)
						{

							if (prteNearby->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 == pe2_n->list_delete->destination->rt_entry_infos.rtu_dst.interfaceAddr.ipv4)
							{


								prteNearby->rt_metric = MAX_COST;

								destination_n* list_destination_tmp;
								list_destination_tmp = (destination_n* )
									MEM_malloc(sizeof(destination_n));

								memset(
									list_destination_tmp,
									0,
									sizeof(destination_n));

								list_destination_tmp->destination = prteNearby;


								list_destination_tmp->next = pe2_n_1->list_delete;
								pe2_n_1->list_delete = list_destination_tmp;



							}
							else
							{
								if (pe2_n->list_delete->destination->rt_entry_infos.rtu_lasthop.interfaceAddr.ipv4 == prteNearby->rt_entry_infos.rtu_dst.interfaceAddr.ipv4)
								{


								}
								else
								{

									//if there is any other adjacent nodes outside the tree, then 

									bInsideNode = FALSE;

								}
							}

						}

						
						topo_dest = topo_dest->next;
					}

					if (!bInsideNode)
					{

						insert_into_tco_node_addr_set(ptna_delete_set, pe2_n->list_delete->destination->rt_entry_infos.rtu_dst.interfaceAddr.ipv4);

					}
				}
			}

			

			destination_n_1 = pe2_n->list_delete;
			pe2_n->list_delete =  pe2_n->list_delete->next;

			

			destination_n_1->next = *plist_destination_delete;
			*plist_destination_delete = destination_n_1;	
		}
	}

}

