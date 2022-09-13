package politics;

import static org.junit.jupiter.api.Assertions.*;

import org.junit.jupiter.api.Test;

class CandidateTest {
	
	/**
	 * Testa il funzionamento del metodo setParty di Candidate, che serve a istanziare un nuovo partito di appartenenza per un candidato.
	 */
	@Test
	void testSetParty() {
		Candidate c = new Candidate("Mattia","Garavaglia");
		Party p = new Party("Gruppo1");
		c.setParty(p);
		
		assertEquals(p,c.getParty());
	}
	
	/**
	 * Testa il funzionameto del metodo equals di Candidate nel caso di confronto tra due Candidate uguali.
	 */
	@Test
	void testEquals() {
		Party p = new Party("Gruppo1");
		Candidate c1 = new Candidate("Mattia","Garavaglia",p);
		Candidate c2 = new Candidate("Mattia", "Garavaglia", p);
		
		assertEquals(c1,c2);
	}
	
	/**
	 * Testa il funzionameto del metodo equals di Candidate nel caso di confronto tra due Candidate diversi.
	 */
	@Test
	void testNotEquals() {
		Party p = new Party("Gruppo1");
		Candidate c1 = new Candidate("Mattia","Garavaglia",p);
		Candidate c2 = new Candidate("Umberto", "Pirovano", p);
		
		assertNotEquals(c1,c2);
	}
}
