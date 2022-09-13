package politics;

import static org.junit.jupiter.api.Assertions.*;

import org.junit.jupiter.api.Test;

class PartyTest {
	
	/**
	 * Testa il funzionameto del metodo equals di Party nel caso di confronto tra due Party uguali.
	 */
	@Test
	void testEquals() {
		Party p1 = new Party("Gruppo1");
		Party p2 = new Party("Gruppo1");
		
		assertEquals(p1,p2);
	}
	
	/**
	 * Testa il funzionameto del metodo equals di Party nel caso di confronto tra due Party diversi.
	 */
	@Test
	void testNotEquals() {
		Party p1 = new Party("Gruppo1");
		Party p2 = new Party("Gruppo2");
		
		assertNotEquals(p1,p2);
	}

}
