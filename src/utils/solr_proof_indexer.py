#!/usr/bin/env python3
"""
Solr Proof Indexer - Uploads completed proofs to Solr for future reference
Builds a growing knowledge base of verified proofs
"""

import json
import requests
import hashlib
import time
from datetime import datetime
from urllib.parse import urljoin

class SolrProofIndexer:
    def __init__(self, solr_base_url="http://localhost:8983/solr"):
        """Initialize Solr indexer for proof storage"""
        self.solr_base_url = solr_base_url
        self.solved_proofs_core = "solved_proofs"
        self.proof_patterns_core = "proof_patterns"
        
        print(f"[SolrIndexer] Initializing with Solr: {solr_base_url}", flush=True)
        self._ensure_cores_exist()
    
    def _ensure_cores_exist(self):
        """Create Solr cores if they don't exist"""
        cores_to_create = [self.solved_proofs_core, self.proof_patterns_core]
        
        for core_name in cores_to_create:
            try:
                # Check if core exists
                response = requests.get(f"{self.solr_base_url}/{core_name}/admin/ping", timeout=5)
                if response.status_code == 200:
                    print(f"[SolrIndexer] Core '{core_name}' exists", flush=True)
                    continue
            except:
                pass
            
            try:
                # Create core
                create_url = f"{self.solr_base_url}/admin/cores"
                params = {
                    'action': 'CREATE',
                    'name': core_name,
                    'configSet': '_default'
                }
                
                response = requests.post(create_url, params=params, timeout=10)
                if response.status_code == 200:
                    print(f"[SolrIndexer] Created core '{core_name}'", flush=True)
                else:
                    print(f"[SolrIndexer] Failed to create core '{core_name}': {response.text}", flush=True)
            
            except Exception as e:
                print(f"[SolrIndexer] Error creating core '{core_name}': {e}", flush=True)
    
    def index_completed_proof(self, theorem_statement, proof_script, bot_name, 
                            confidence=1.0, verification_time=0.0, context=""):
        """Index a completed proof in Solr"""
        
        # Generate unique ID for the proof
        proof_id = self._generate_proof_id(theorem_statement, proof_script)
        
        # Extract proof features for better searching
        features = self._extract_proof_features(theorem_statement, proof_script)
        
        # Create Solr document
        doc = {
            'id': proof_id,
            'theorem_statement_s': theorem_statement,
            'proof_script_s': proof_script,
            'bot_name_s': bot_name,
            'confidence_f': confidence,
            'verification_time_f': verification_time,
            'context_s': context,
            'timestamp_dt': datetime.utcnow().isoformat() + 'Z',
            'indexed_date_dt': datetime.utcnow().isoformat() + 'Z',
            
            # Searchable features
            'theorem_type_s': features['theorem_type'],
            'proof_tactics_ss': features['tactics_used'],
            'complexity_i': features['complexity'],
            'domain_keywords_ss': features['domain_keywords'],
            'induction_used_b': features['uses_induction'],
            'arithmetic_used_b': features['uses_arithmetic'],
            'logic_used_b': features['uses_logic'],
            
            # Full text search fields
            'content_txt': f"{theorem_statement} {proof_script}",
            'searchable_text_txt': features['searchable_text']
        }
        
        # Upload to Solr
        success = self._upload_document(self.solved_proofs_core, doc)
        
        if success:
            print(f"[SolrIndexer] ✅ Indexed proof: {proof_id[:16]}...", flush=True)
            
            # Also index proof patterns for ML training
            self._index_proof_patterns(theorem_statement, proof_script, features)
            
            return proof_id
        else:
            print(f"[SolrIndexer] ❌ Failed to index proof", flush=True)
            return None
    
    def _generate_proof_id(self, theorem_statement, proof_script):
        """Generate unique ID for proof"""
        content = f"{theorem_statement}|{proof_script}"
        return hashlib.sha256(content.encode()).hexdigest()
    
    def _extract_proof_features(self, theorem_statement, proof_script):
        """Extract searchable features from proof"""
        import re
        
        # Determine theorem type
        theorem_type = "unknown"
        if re.search(r'forall.*nat', theorem_statement, re.IGNORECASE):
            theorem_type = "arithmetic"
        elif re.search(r'forall.*list', theorem_statement, re.IGNORECASE):
            theorem_type = "list_theory"
        elif re.search(r'exists', theorem_statement, re.IGNORECASE):
            theorem_type = "existential"
        elif re.search(r'\/\\|\\\/|->', theorem_statement, re.IGNORECASE):
            theorem_type = "propositional_logic"
        elif re.search(r'=', theorem_statement, re.IGNORECASE):
            theorem_type = "equality"
        
        # Extract tactics used
        tactic_patterns = [
            r'\binduction\b', r'\bauto\b', r'\btrivial\b', r'\breflexivity\b',
            r'\bring\b', r'\blia\b', r'\bomega\b', r'\bsplit\b', r'\bleft\b', 
            r'\bright\b', r'\bintro\b', r'\brewrite\b', r'\bsimpl\b',
            r'\bexists\b', r'\bapply\b', r'\bexact\b', r'\btauto\b'
        ]
        
        tactics_used = []
        for pattern in tactic_patterns:
            if re.search(pattern, proof_script, re.IGNORECASE):
                tactics_used.append(pattern[2:-2])  # Remove \b markers
        
        # Domain keywords
        domain_keywords = []
        keywords = ['nat', 'list', 'Prop', 'bool', 'option', 'tree', 'plus', 'mult', 'app']
        for keyword in keywords:
            if re.search(rf'\b{keyword}\b', theorem_statement, re.IGNORECASE):
                domain_keywords.append(keyword)
        
        # Complexity estimation
        complexity = len(proof_script.split('\n')) + theorem_statement.count('forall') * 2
        
        return {
            'theorem_type': theorem_type,
            'tactics_used': tactics_used,
            'complexity': complexity,
            'domain_keywords': domain_keywords,
            'uses_induction': 'induction' in tactics_used,
            'uses_arithmetic': any(t in tactics_used for t in ['ring', 'lia', 'omega']),
            'uses_logic': any(t in tactics_used for t in ['split', 'left', 'right', 'tauto']),
            'searchable_text': f"{theorem_type} {' '.join(tactics_used)} {' '.join(domain_keywords)}"
        }
    
    def _index_proof_patterns(self, theorem_statement, proof_script, features):
        """Index proof patterns for ML training data"""
        pattern_id = hashlib.md5(f"{features['theorem_type']}_{theorem_statement[:50]}".encode()).hexdigest()
        
        pattern_doc = {
            'id': pattern_id,
            'theorem_pattern_s': self._extract_theorem_pattern(theorem_statement),
            'proof_pattern_s': self._extract_proof_pattern(proof_script),
            'theorem_type_s': features['theorem_type'],
            'success_tactics_ss': features['tactics_used'],
            'complexity_i': features['complexity'],
            'example_theorem_s': theorem_statement,
            'example_proof_s': proof_script,
            'timestamp_dt': datetime.utcnow().isoformat() + 'Z'
        }
        
        self._upload_document(self.proof_patterns_core, pattern_doc)
    
    def _extract_theorem_pattern(self, theorem_statement):
        """Extract general pattern from theorem statement"""
        import re
        
        # Replace specific names with placeholders
        pattern = re.sub(r'\b[a-z]\b', 'VAR', theorem_statement)  # Replace single variables
        pattern = re.sub(r'\b\d+\b', 'NUM', pattern)  # Replace numbers
        pattern = re.sub(r'\b[A-Z][a-zA-Z]*\b', 'TYPE', pattern)  # Replace type names
        
        return pattern
    
    def _extract_proof_pattern(self, proof_script):
        """Extract general pattern from proof script"""
        import re
        
        # Extract just the tactic sequence
        lines = proof_script.split('\n')
        tactics = []
        
        for line in lines:
            line = line.strip()
            if line and not line.startswith('(*'):
                # Extract main tactic
                tactic = re.split(r'[;\.]', line)[0].strip()
                if tactic:
                    tactics.append(tactic)
        
        return ' -> '.join(tactics)
    
    def _upload_document(self, core_name, document):
        """Upload document to Solr core"""
        try:
            url = f"{self.solr_base_url}/{core_name}/update/json/docs"
            headers = {'Content-Type': 'application/json'}
            
            # Upload document
            response = requests.post(url, json=document, headers=headers, timeout=10)
            
            if response.status_code == 200:
                # Commit the changes
                commit_url = f"{self.solr_base_url}/{core_name}/update?commit=true"
                commit_response = requests.post(commit_url, timeout=5)
                
                return commit_response.status_code == 200
            
            return False
        
        except Exception as e:
            print(f"[SolrIndexer] Upload error: {e}", flush=True)
            return False
    
    def search_similar_proofs(self, theorem_statement, max_results=10):
        """Search for similar proofs in the index"""
        try:
            # Extract key terms for search
            import re
            terms = re.findall(r'\b(?:forall|nat|list|Prop|exists|\+|\*|=|<=)\b', theorem_statement)
            query = ' OR '.join(terms[:5]) if terms else theorem_statement[:50]
            
            url = f"{self.solr_base_url}/{self.solved_proofs_core}/select"
            params = {
                'q': f'content_txt:({query})',
                'rows': max_results,
                'fl': 'id,theorem_statement_s,proof_script_s,confidence_f,bot_name_s',
                'wt': 'json'
            }
            
            response = requests.get(url, params=params, timeout=5)
            if response.status_code == 200:
                data = response.json()
                return data['response']['docs']
        
        except Exception as e:
            print(f"[SolrIndexer] Search error: {e}", flush=True)
        
        return []
    
    def get_stats(self):
        """Get statistics about indexed proofs"""
        stats = {}
        
        for core_name in [self.solved_proofs_core, self.proof_patterns_core]:
            try:
                url = f"{self.solr_base_url}/{core_name}/select"
                params = {'q': '*:*', 'rows': 0, 'wt': 'json'}
                
                response = requests.get(url, params=params, timeout=5)
                if response.status_code == 200:
                    data = response.json()
                    stats[core_name] = data['response']['numFound']
                else:
                    stats[core_name] = 0
            
            except Exception as e:
                stats[core_name] = f"Error: {e}"
        
        return stats

# Example usage function
def test_indexer():
    """Test the Solr proof indexer"""
    indexer = SolrProofIndexer()
    
    # Test indexing a proof
    theorem = "forall n : nat, n + 0 = n"
    proof = "induction n; simpl; auto with arith."
    
    proof_id = indexer.index_completed_proof(
        theorem_statement=theorem,
        proof_script=proof,
        bot_name="test_bot",
        confidence=0.95,
        verification_time=0.123
    )
    
    print(f"Indexed proof with ID: {proof_id}")
    
    # Test searching
    similar = indexer.search_similar_proofs(theorem)
    print(f"Found {len(similar)} similar proofs")
    
    # Show stats
    stats = indexer.get_stats()
    print(f"Solr stats: {stats}")

if __name__ == "__main__":
    test_indexer()