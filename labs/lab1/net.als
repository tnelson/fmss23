/* ====================================================================
A SIMPLIFIED MODEL OF NETWORK STATE 
==================================================================== */
/* --------------------------------------------------------------------
TYPES
-------------------------------------------------------------------- */

sig Name { }                            -- the name of a network member
   
sig LinkIdent, SessionIdent { }
 
abstract sig Command { }
   one sig Receive, Drop extends Command { }
one sig Self { }

sig NetHdr
   {  src, dst: Name, sessionIdent: SessionIdent  }
fact NetHdrsAreRecords { all h, h": NetHdr |
   (  h.sessionIdent = h".sessionIdent 
   && h.src = h".src && h.dst = h".dst  ) 
   => h = h" }           -- if an object is a "record," the identity of
                        -- an instance depends only on its field values

sig Link { 
   sndr: Name, 
   sndrIdent: LinkIdent,
   rcvr: Name,
   rcvrIdent: LinkIdent
} 
-- Note that links are not records; there can be two distinct 
-- individuals that happen to have the same field values.
   
sig ForwardTable { frows:
   (LinkIdent + Self) -> NetHdr -> (LinkIdent + Command)  }

/* --------------------------------------------------------------------
NETWORK STATES
   There are many versions of reachable here, only one of which is
usable.  The mnemonic names explain them somewhat.  For pedagogical
purposes, the names must be obscured!
-------------------------------------------------------------------- */

sig NetworkState {
-- Network components (domain knowledge).
   members: set Name,        -- every member has at least a unique name
   disj infras, users: set members,    -- trusted and untrusted members
   links: set Link,
   outLinks, inLinks: members -> LinkIdent -> links,         -- derived
-- Network traffic (domain knowledge).
   sendTable: members -> NetHdr,
   receiveTable: members -> NetHdr,
-- Behavior of network members (specification).
   forwardTables: members -> lone ForwardTable,
   oneStep: NetHdr -> links -> links,              -- all derived below
   reachableWithMandatoryForwarding: NetHdr -> Name -> Name,
   reachableWithoutEndpointInfo: NetHdr -> Name -> Name,
   reachableWithEndpointInfo: NetHdr -> Name -> Name,
   endToEndReachable: NetHdr -> Name -> Name,
   reachable: NetHdr -> Name -> Name
}  {
-- Network topology.
   -- Each member is an infrastructure member or user.
      infras + users = members
   -- All links have at least one endpoint that is a member.
      all k: links | some ((k.sndr + k.rcvr) & members) 
   -- There are no self-links.
      all k: links | k.sndr != k.rcvr
   -- For each member, its local linkIdents are disjoint.
      all disj k0, k1: links | 
      (   (k0.sndr = k1.sndr => k0.sndrIdent != k1.sndrIdent)
      &&  (k0.rcvr = k1.rcvr => k0.rcvrIdent != k1.rcvrIdent)
      &&  (k0.sndr = k1.rcvr => k0.sndrIdent != k1.rcvrIdent)  )
   -- Derivation of inLinks and outLinks.
      outLinks = { m: members, i: LinkIdent, k: links |
         k.sndr = m && k.sndrIdent = i                }         
      inLinks = { m: members, i: LinkIdent, k: links |
         k.rcvr = m && k.rcvrIdent = i               }
-- Behavior of network members.  
   -- The forwardTable.  The absence of a matching table entry means 
   -- that an incoming packet is dropped.
      -- Consistency: All inLinks and outLinks are real.
      all m: members, kin: 
         (((m.forwardTables).frows).(LinkIdent + Command)).NetHdr |
         ( (m -> kin) in inLinks.links || kin in Self )
      all m: members, kout:
              NetHdr.((LinkIdent + Self).((m.forwardTables).frows)) |
         kout ! in Command => (m -> kout) in outLinks.links
      -- A forwardTable can yield multiple outLinks for replication for
      -- allCast service.  In addition to yielding multiple outLinks, 
      -- it can yield a Receive command.  Otherwise it is 
      -- deterministic.  If there is no matching entry for an incoming
      -- packet, it is dropped.
         all m: members, ki: LinkIdent + Command, h: NetHdr |
            (  lone h.(ki.((m.forwardTables).frows))
            || h.(ki.((m.forwardTables).frows)) in 
                  (LinkIdent + Receive)            )
-- Reachability.
      oneStep = {  h: NetHdr, disj k, k": links |
         some m: Name, kin, kout: LinkIdent |
            (m -> kin -> k) in inLinks 
         && (m -> kout -> k") in outLinks
         && (kin -> h -> kout) in (m.forwardTables).frows  }
      reachableWithMandatoryForwarding = {  h: NetHdr, m, m": Name | 
         some k, k": links | 
            m in k.sndr && m" in k".rcvr && (k -> k") in ^(h.oneStep) }
      reachableWithoutEndpointInfo = {  h: NetHdr, m, m": Name | 
         some k, k": links | 
            m in k.sndr && m" in k".rcvr 
         && (  k = k" || (k -> k") in ^(h.oneStep)  )          }
      reachableWithEndpointInfo = {  h: NetHdr, m, m": Name | 
         some k, k": links, kin, kout: LinkIdent | 
            (m -> kout -> k) in outLinks
         && (m" -> kin -> k") in inLinks
         && (h -> kout) in 
               (LinkIdent + Self).((m.forwardTables).frows)
         && (kin -> h) in 
               ((m".forwardTables).frows).(LinkIdent + Receive)
         && (  k = k" || (k -> k") in ^(h.oneStep)  )                }
      endToEndReachable = {  h: NetHdr, m, m": Name | 
         some k, k": links, kin, kout: LinkIdent | 
            (m -> kout -> k) in outLinks
         && (m" -> kin -> k") in inLinks
         && (h -> kout) in Self.((m.forwardTables).frows)
         && (kin -> h) in ((m".forwardTables).frows).Receive
         && (  k = k" || (k -> k") in ^(h.oneStep)  )      }
      reachable = reachableWithEndpointInfo
}

/* --------------------------------------------------------------------
PROPERTIES OF NETWORK TOPOLOGY (domain knowledge)
-------------------------------------------------------------------- */

pred No_external_links [n: NetworkState] {
   all k: n.links | (k.sndr + k.rcvr) in n.members  }

pred Fully_connected [n: NetworkState] {
-- A network in which there is a link from each member to each other 
-- member.  It does not matter whether the members are infras or users, 
-- because no forwarding is necessary.
   all disj m, m": n.members | some k: n.links |
      k.sndr = m && k.rcvr = m"                }

pred Hub_and_spoke [n: NetworkState] {
   -- There is one forwarder, at the hub.
   one n.infras
   -- Users are fully connected to the forwarder.
   all m: n.infras, m": n.users |
      some disj k, k": n.links |
         (  k.sndr = m && k.rcvr = m" && k".sndr = m" && k".rcvr = m  )
   -- Users are not directly connected to each other.
   no k: n.links | k.sndr + k.rcvr in n.users                
 }

pred One_way_ring [n: NetworkState] {
   no n.users 
   -- Links form a one-way ring.
   let connections = { disj m0, m1: Name |
      some k: n.links | m0 = k.sndr && m1 = k.rcvr } |
   (  connections in n.members one -> one n.members 
   && all m, m": n.members | (m -> m") in ^connections  )  }

sig SpanningTreeState in NetworkState {
   root: members,
   disj downLinks, upLinks: set links,
   downGraph: members -> members      }                      -- derived
{
   links = downLinks + upLinks
   some members - root
-- All links are in directional pairs.
   all dk: downLinks | one uk: upLinks | 
      (  dk.sndr = uk.rcvr && dk.rcvr = uk.sndr)
   all uk: upLinks | one dk: downLinks |
      (  dk.sndr = uk.rcvr && dk.rcvr = uk.sndr)
   downGraph = {  up, down: members |
      some dk: downLinks | up = dk.sndr && down = dk.rcvr  }
-- The graph of downLinks is a tree.
   all m: members - root | m in root.(^downGraph)
   no m: members | m in m.(^downGraph)
   all m: members - root | one downGraph.m
-- Note that a spanning-tree network can have external links that are
-- not in the graph.
}

/* --------------------------------------------------------------------
PROPERTIES OF NETWORK TRAFFIC (domain knowledge, with a threat model)
-------------------------------------------------------------------- */

pred Fully_active [n: NetworkState] {
-- A network with a session from each member to each other member.
   all disj m, m": n.members | some h: NetHdr |
      h.src = m && (m -> h) in n.sendTable
   && h.dst = m" && (m" -> h) in n.receiveTable  }

pred Sending_is_authentic [n: NetworkState] {
-- Members only send packets with their own name in the source field.
   all m: n.members, h: NetHdr |
      (m -> h) in n.sendTable => h.src = m  }

pred Receiving_is_authentic [n: NetworkState] {
-- Members only receive packets with their own name in the destination
-- field.
   all m: n.members, h: NetHdr |
      (m -> h) in n.receiveTable => h.dst = m            }

pred Traffic_is_consistent [n: NetworkState] {
-- Sends and receives go together.
   all h: NetHdr |     (some m: Name | (m -> h) in n.sendTable)
                   <=> (some m: Name | (m -> h) in n.receiveTable)  }

pred Traffic_is_symmetric [n: NetworkState] {
-- The traffic model only includes two-way traffic.
   Traffic_is_consistent [n]
   all h: NetHdr, m, m": n.members |
   (  (m -> h) in n.sendTable && (m" -> h) in n.receiveTable  )
   => (some h": NetHdr |
         (m" -> h") in n.sendTable && (m -> h") in n.receiveTable)  }

/* --------------------------------------------------------------------
PROPERTIES OF NETWORK BEHAVIOR: SPECIFICATIONS
-------------------------------------------------------------------- */

pred No_routing_loops [n: NetworkState] {
   all h: NetHdr | no k: n.links | (k -> k) in ^(h.(n.oneStep)) }

pred Deterministic_forwarding [n: NetworkState] {
   all m: n.members, ki: LinkIdent + Self, h: NetHdr |
      lone h.(ki.(m.((n.forwardTables).frows)))      }

/* --------------------------------------------------------------------
PROPERTIES OF NETWORK BEHAVIOR: POSSIBLE REQUIREMENTS
-------------------------------------------------------------------- */

pred Network_satisfies_communication_demands [n: NetworkState] {
-- Communication demands are given by the send and receive tables.
   all m, m": n.members, h: NetHdr |
   (  (m -> h) in n.sendTable && (m" -> h) in n.receiveTable  )
   => (h -> m -> m") in n.reachable                             }

pred Fully_reachable [n: NetworkState] {
-- Every member can reach every other member.
   all disj m, m": n.members |
      some h: NetHdr | (h -> m -> m") in n.reachable  }

pred Only_authentic_traffic_delivered [n: NetworkState] {
-- A possible security requirement.  The alternative definition is used
-- to challenge reachableWithoutEndpointInfo. 
   all m: n.members, mud: n.users, h: NetHdr |
      (h -> m -> mud) in n.reachable 
      => (some mus: n.users |
            h.src = mus && (h -> mus -> mud) in n.reachable  )  }
/* alternative (bad) definition
      (h -> m -> mud) in n.reachableWithoutEndpointInfo 
      => (some mus: n.users |
            h.src = mus 
         && (h -> mus -> mud) in n.reachableWithoutEndpointInfo  )  }
*/

pred Delivery_is_blocked [n: NetworkState, disj bad, good: Name] {
-- A possible security requirement.
   (bad + good) in n.users
   (bad -> good) ! in NetHdr.(n.reachable)                       }

pred Delivery_is_filtered [n: NetworkState, disj filter, good: Name] {
-- A possible security requirement.
-- This is a challenge to endToEndReachable, which misses middleboxes.
   filter in n.infras && good in n.users
   all h: NetHdr, suspect: n.users |
      (h -> suspect -> good) in n.reachable 
   => (h -> suspect -> filter) in n.reachable                        }
/* alternative (bad) definition
      (h -> suspect -> good) in n.endToEndReachable 
   => (h -> suspect -> filter) in n.endToEndReachable                }
*/

/* ====================================================================
run P for 1 but
   N NetworkState,
   M Name, L<=K LinkIdent, K Link, D SessionIdent, D NetHdr,
   NxM ForwardTable
==================================================================== */
/* ====================================================================
VALIDATION AND VERIFICATION ARCHIVE
==================================================================== */
/* --------------------------------------------------------------------
TESTS AND SANITY CHECKS FOR NETWORK TOPOLOGY
-------------------------------------------------------------------- */

pred Topology_test_1 [n: NetworkState] { 
   some n.links && No_external_links [n]  }
run Topology_test_1 for 1 but 3 Name,2 LinkIdent,6 Link,3 ForwardTable

pred Topology_test_2 [n: NetworkState] { 
   ! No_external_links [n]  }
run Topology_test_2 for 1 but 3 Name,2 LinkIdent,6 Link,3 ForwardTable

pred Topology_test_3 [n: NetworkState] { 
   # n.members = 3 && Fully_connected[n]  }
run Topology_test_3 for 1 but 3 Name,4 LinkIdent,6 Link,3 ForwardTable   

pred Topology_test_4 [n: NetworkState] { 
   # n.members = 3 && Fully_connected[n] && No_external_links [n]  }
run Topology_test_4 for 1 but 3 Name,4 LinkIdent,6 Link,3 ForwardTable

pred Topology_test_5 [n: NetworkState] { 
   # n.members = 3 && Fully_connected[n] && ! No_external_links [n]  }
run Topology_test_5 for 1 but 5 Name,6 LinkIdent,8 Link,3 ForwardTable

pred Topology_test_6 [n: NetworkState] { 
   # n.members = 4 && Hub_and_spoke [n]  }
run Topology_test_6 for 1 but 4 Name,6 LinkIdent,6 Link,4 ForwardTable

pred Topology_test_7 [n: NetworkState] { 
   Hub_and_spoke [n] && No_external_links [n]  }
run Topology_test_7 for 1 but 4 Name,6 LinkIdent,8 Link,4 ForwardTable

pred Topology_test_8 [n: NetworkState] { 
   Hub_and_spoke [n] && ! No_external_links [n]  }
run Topology_test_8 for 1 but 4 Name,6 LinkIdent,8 Link,4 ForwardTable

pred Topology_test_9 [n: NetworkState] { 
   # n.members = 4 && One_way_ring [n]  }
run Topology_test_9 for 1 but 4 Name,2 LinkIdent,4 Link,4 ForwardTable

assert One_way_ring_has_no_external_links {
   all n: NetworkState | One_way_ring [n] => No_external_links [n]  }
check One_way_ring_has_no_external_links for 1 but
   5 Name, 4 LinkIdent, 8 Link, 5 ForwardTable

pred Topology_test_10 [n: SpanningTreeState] {
   # n.members = 5 && ! Hub_and_spoke [n]  }
run Topology_test_10 for 1 but
   5 Name, 4 LinkIdent, 8 Link, 5 ForwardTable

pred Topology_test_11[n: SpanningTreeState] {
      # n.members = 5 && Hub_and_spoke [n]  }
run Topology_test_11 for 1 but
   5 Name, 8 LinkIdent, 8 Link, 5 ForwardTable

pred Topology_test_12 [n: SpanningTreeState] { ! No_external_links [n] }
run Topology_test_12 for 1 but
   5 Name, 6 LinkIdent, 8 Link, 5 ForwardTable

assert Nontrivial_ring_cannot_be_spanning_tree {
   all n: NetworkState |
      (# members >= 3 && One_way_ring [n]) 
   => n ! in SpanningTreeState                 }
check Nontrivial_ring_cannot_be_spanning_tree for 1 but
   4 Name, 4 LinkIdent, 8 Link, 4 ForwardTable

/* --------------------------------------------------------------------
TESTS AND SANITY CHECKS FOR NETWORK TRAFFIC
   From now on, the validation shown is selective, rather than closer
to exhaustive, as it is in the topology section, and as it should be.
-------------------------------------------------------------------- */

pred Traffic_test_1 [n: NetworkState] {
   # n.members = 4 && One_way_ring [n] && Fully_active [n]  }
run Traffic_test_1 for 1 but
   4 Name,2 LinkIdent,4 Link,12 SessionIdent,12 NetHdr,4 ForwardTable

pred Traffic_test_2 [n: NetworkState] {
   # n.members = 4 && Hub_and_spoke [n] 
   && Sending_is_authentic [n] && ! Receiving_is_authentic [n]  }
run Traffic_test_2 for 1 but
   4 Name,6 LinkIdent,6 Link,4 SessionIdent,4 NetHdr,4 ForwardTable

pred Traffic_test_3 [n: NetworkState] {
   # n.members = 4 && n in SpanningTreeState
   && ! Sending_is_authentic [n] && Receiving_is_authentic [n]  }
run Traffic_test_3 for 1 but
   4 Name,6 LinkIdent,6 Link,6 SessionIdent,6 NetHdr,4 ForwardTable

pred Traffic_test_4 [n: NetworkState] {
   # n.members = 4 && n in SpanningTreeState && ! Hub_and_spoke [n]
   Sending_is_authentic [n] && Receiving_is_authentic [n]  
   Traffic_is_symmetric [n]                                       }
run Traffic_test_4 for 1 but
   4 Name,6 LinkIdent,6 Link,6 SessionIdent,6 NetHdr,4 ForwardTable

/* --------------------------------------------------------------------
TESTS FOR NETWORK BEHAVIOR (SPECIFICATIONS)
-------------------------------------------------------------------- */

pred Behavior_test_1 [n: NetworkState] { 
   No_routing_loops [n] && Deterministic_forwarding [n]  }
run Behavior_test_1 for 1 but 
   4 Name, 3 LinkIdent, 6 Link, 2 NetHdr, 4 ForwardTable

pred Behavior_test_2 [n: NetworkState] { 
   No_routing_loops [n] && ! Deterministic_forwarding [n]  }
run Behavior_test_2 for 1 but 
   4 Name, 3 LinkIdent, 6 Link, 2 NetHdr, 4 ForwardTable

pred Behavior_test_3 [n: NetworkState] { 
   ! No_routing_loops [n] && Deterministic_forwarding [n]  }
run Behavior_test_3 for 1 but 
   4 Name, 3 LinkIdent, 6 Link, 2 NetHdr, 4 ForwardTable

pred Behavior_test_4 [n: NetworkState] { 
   ! No_routing_loops [n] && ! Deterministic_forwarding [n]  }
run Behavior_test_4 for 1 but 
   4 Name, 3 LinkIdent, 6 Link, 2 NetHdr, 4 ForwardTable

pred Behavior_test_5 [n: SpanningTreeState] { 
   No_routing_loops [n] && Deterministic_forwarding [n]  }
run Behavior_test_5 for 1 but 
   4 Name, 3 LinkIdent, 6 Link, 2 NetHdr, 4 ForwardTable

pred Behavior_test_6 [n: NetworkState] { 
      ! No_routing_loops [n] && ! Deterministic_forwarding [n]
   && Fully_connected [n]                                    }
run Behavior_test_6 for 1 but 
   4 Name, 4 LinkIdent, 6 Link, 2 NetHdr, 4 ForwardTable

/* --------------------------------------------------------------------
TESTS AND SANITY CHECKS ABOUT NETWORK BEHAVIOR (POSSIBLE REQUIREMENTS)
-------------------------------------------------------------------- */

pred Fully_reachable_does_not_satisfy_all_demands [n: NetworkState] {
      Fully_reachable [n] 
   && ! Network_satisfies_communication_demands [n]                 }
-- Instances possible because full reachability does not include
-- self-reachability.
run Fully_reachable_does_not_satisfy_all_demands for 1 but
   3 Name, 3 LinkIdent, 4 Link, 3 NetHdr, 3 ForwardTable

pred Network_exceeds_communication_demands [n: NetworkState] {
      some n.sendTable && some n.receiveTable
   && Sending_is_authentic [n] && Receiving_is_authentic [n]
   && Traffic_is_symmetric [n] && ! Only_authentic_traffic_delivered[n]
   && Network_satisfies_communication_demands [n]                     }
run Network_exceeds_communication_demands for 1 but
   3 Name, 3 LinkIdent, 4 Link, 3 NetHdr, 3 ForwardTable

assert Reachability_domain_is_members { all n: NetworkState |
   NetHdr.(n.reachable) in (n.members -> n.members)         }
-- Reachability could have been defined to include external members!
check Reachability_domain_is_members for 1 but
   5 Name, 3 LinkIdent, 6 Link, 2 NetHdr, 5 ForwardTable

assert Blocking_precludes_fully_reachable { all n: NetworkState |
      (some disj m, m": n.members | Delivery_is_blocked [n, m, m"])
   => ! Fully_reachable [n]                                       }
check Blocking_precludes_fully_reachable for 1 but
   5 Name, 3 LinkIdent, 6 Link, 2 NetHdr, 5 ForwardTable

/* --------------------------------------------------------------------
SANITY CHECKS ON SPECIALIZED NETWORKS
-------------------------------------------------------------------- */
 
one sig m0, m1, m2, m3 extends Name {}
one sig k01, k12, k23 extends Link {}
one sig j0, j1 extends LinkIdent {}  
one sig h, h0, h1 extends NetHdr {}

pred TestNet [n: NetworkState] {
   n.members = m0 + m1 + m2 + m3 && n.users = m0 + m3
   n.links = k01 + k12 + k23
   k01.sndr = m0 && k12.sndr = m1 && k23.sndr = m2
   k01.sndrIdent = j1 && k12.sndrIdent = j1 && k23.sndrIdent = j1
   k01.rcvr = m1 && k12.rcvr = m2 && k23.rcvr = m3
   k01.rcvrIdent = j0 && k12.rcvrIdent = j0 && k23.rcvrIdent = j0
   h.src = m0 && h.dst = m3
   (m0.(n.forwardTables)).frows = (Self -> h -> j1)
   (m1.(n.forwardTables)).frows = (j0 -> h -> j1)
   (m2.(n.forwardTables)).frows = (j0 -> h -> j1)
   (m3.(n.forwardTables)).frows = (j0 -> h -> Receive) 
}
-- Looking at "reachableWithMandatoryForwarding" in this instance, we
-- can see that it is an invalid definition, not at all what we mean.
run TestNet for 1 but 
   4 Name, 2 LinkIdent, 3 Link, 3 NetHdr, 4 ForwardTable

-- To check this assertion, first change "reachable" in the requirement
-- to "reachableWithoutEndpointInfo".  The assertion will not hold.  
-- Then change back to "reachable", and it will hold.
assert TestNet_is_secure {
   all n: NetworkState | TestNet [n] 
   => Only_authentic_traffic_delivered [n]  }
check TestNet_is_secure for 1 but 
   4 Name, 2 LinkIdent, 3 Link, 3 NetHdr, 4 ForwardTable

-- To check this assertion, first change "reachable" in the requirement
-- to "endToEndReachable".  The assertion will not hold.  Then change
-- back to "reachable", and it will hold.
assert TestNet_is_filtered {
   all n: NetworkState | TestNet [n] 
   => Delivery_is_filtered [n, m2, m3]  }
check TestNet_is_filtered for 1 but 
   4 Name, 2 LinkIdent, 3 Link, 3 NetHdr, 4 ForwardTable

assert Hub_and_spoke_nonreachability_theorem {
-- In a hub-and-spoke network, if the user members do not forward and
-- the hub does not send or receive, then the hub should not be 
-- reachable from itself.
   all n: NetworkState | {
      Hub_and_spoke [n]
      all f: n.infras |
         let ftbl = ((f.(n.forwardTables)).frows) |
      (  -- The hub does not receive packets.
         Receive ! in NetHdr.((LinkIdent + Self).ftbl)
         -- The hub does not send packets.
      && Self ! in (ftbl.LinkIdent).NetHdr           )
      all u: n.users |
         let ftbl = ((u.(n.forwardTables)).frows) |
         -- Users do not forward packets.
         no LinkIdent<:((ftbl.LinkIdent).NetHdr)
   }  => all f: n.infras | 
         (f -> f) ! in NetHdr.(n.reachable)          }
check Hub_and_spoke_nonreachability_theorem for 1 but
   4 Name, 6 LinkIdent, 6 Link, 2 NetHdr, 4 ForwardTable

assert One_way_ring_theorem {
-- If members receive packets with their own name as destination and 
-- forward other packets from their inLinks to their outLinks, then 
-- all members are reachable from all other members.  Note that this
-- formulation of the theorem would not work if the network had
-- external links.
   all n: NetworkState |
   (  One_way_ring [n] && No_external_links [n]
   && all m: n.members, h: NetHdr |
      h.dst = m =>
      (  (let kin = (m.(n.inLinks)).Link |
         let kout = (m.(n.outLinks)).Link |
         let ftbl = ((m.(n.forwardTables)).frows) |
            h.(kin.ftbl) = Receive && (Self -> h -> kout) in ftbl  )
      && (all m": n.members - m | 
            let kin = (m".(n.inLinks)).Link |
            let kout = (m".(n.outLinks)).Link |
            let ftbl = ((m".(n.forwardTables)).frows) |
               (kin -> h -> kout) in ftbl             )
      )
   )  => (  all m, m": n.members, h: NetHdr | h.dst = m" 
            => (h -> m -> m") in n.reachable           )           }
check One_way_ring_theorem for 1 but
   5 Name, 2 LinkIdent, 5 Link, 5 ForwardTable, 5 NetHdr
