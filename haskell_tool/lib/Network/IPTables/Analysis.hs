module Network.IPTables.Analysis
( toSimpleFirewall
, toSimpleFirewallWithoutInterfaces
, certifySpoofingProtection
, accessMatrix
)
where

--import Network.IPTables.Ruleset -- show instances
import Network.IPTables.IsabelleToString (Word32)
import Network.IPTables.IpassmtParser (IsabelleIpAssmt) --nicer type --TODO: move?

import qualified Network.IPTables.Generated as Isabelle


-- checks that the simple_firewall has a default rule. Not having a default rule
-- is not actually an assumption required by the theorems but it would indicate
-- a broken parser
-- Throws an exception
--TODO: does Haskell have an assert statement?
check_simpleFw_default_rule :: [Isabelle.Simple_rule Word32] -> [Isabelle.Simple_rule Word32]
check_simpleFw_default_rule rs =
    if 
        Isabelle.has_default_policy rs
    then
        rs
    else
        error "simple firewall does not have a default rule!"


-- all functions must only be called with a simple_ruleset. TODO: check this?


-- Theorem: new_packets_to_simple_firewall_overapproximation
toSimpleFirewall :: [Isabelle.Rule (Isabelle.Common_primitive Word32)] -> [Isabelle.Simple_rule Word32]
toSimpleFirewall = check_simpleFw_default_rule . 
                        Isabelle.to_simple_firewall . Isabelle.upper_closure . 
                            Isabelle.optimize_matches Isabelle.abstract_for_simple_firewall .
                                Isabelle.upper_closure . Isabelle.packet_assume_new 

-- Theorem: to_simple_firewall_without_interfaces
toSimpleFirewallWithoutInterfaces :: IsabelleIpAssmt -> [Isabelle.Rule (Isabelle.Common_primitive Word32)] -> [Isabelle.Simple_rule Word32]
toSimpleFirewallWithoutInterfaces ipassmt = check_simpleFw_default_rule . Isabelle.to_simple_firewall_without_interfaces ipassmt



-- Theorem: no_spoofing_executable_set
-- ipassmt -> rs -> (warning_and_debug, spoofing_certification_results)
certifySpoofingProtection :: IsabelleIpAssmt -> [Isabelle.Rule (Isabelle.Common_primitive Word32)] -> ([String], [(Isabelle.Iface, Bool)])
certifySpoofingProtection ipassmt rs = (warn_defined ++ debug_ipassmt, certResult)
    where -- fuc: firewall under certification, prepocessed
          -- no_spoofing_executable_set requires normalized_nnf_match. Isabelle.upper_closure guarantees this.
          -- It also guarantees that if we start from a simple_ruleset, it remains a simple ruleset.
          -- Theorem: no_spoofing_executable_set_preprocessed
          fuc = Isabelle.upper_closure $ Isabelle.packet_assume_new rs
          warn_defined = if (Isabelle.ipassmt_sanity_defined fuc ipassmtMap) -- fuc needs to be nnf-normalized
                         then []
                         else ["WARNING There are some interfaces in your firewall ruleset which are not defined in your ipassmt."]
          debug_ipassmt = Isabelle.debug_ipassmt ipassmt fuc
          ipassmtMap = Isabelle.map_of_ipassmt ipassmt
          certResult = map (\ifce -> (ifce, Isabelle.no_spoofing_iface ifce ipassmtMap fuc)) interfaces
              where interfaces = map fst ipassmt

-- Theorem: access_matrix
-- TODO: in Main.hs we directly have upper_simple available. Make a specific function which gets upper_simple?
-- This is slightly faster (tested!) but dangerously because someone might call it wrong (e.g. with a firewall with interfaces)
accessMatrix :: IsabelleIpAssmt -> [Isabelle.Rule (Isabelle.Common_primitive Word32)] -> Integer -> Integer -> ([(String, String)], [(String, String)])
accessMatrix ipassmt rs sport dport = if sport >= 65536 || dport >= 65536 then error "ports are 16 bit"
    -- Theorem: access_matrix
    else Isabelle.access_matrix_pretty parts_connection upper_simple
    -- Theorem: to_simple_firewall_without_interfaces
    where upper_simple = toSimpleFirewallWithoutInterfaces ipassmt rs
          parts_connection = Isabelle.mk_parts_connection_TCP (Isabelle.integer_to_16word sport) (Isabelle.integer_to_16word dport)
