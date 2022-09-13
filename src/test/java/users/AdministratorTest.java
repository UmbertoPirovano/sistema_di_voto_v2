package users;

import static org.junit.jupiter.api.Assertions.*;

import org.junit.jupiter.api.Test;

class AdministratorTest {

	/**
	 * Testa il funzionameto del metodo equals di Administrator nel caso di confronto tra due Administrator uguali.
	 */
	@Test
	void testEquals() {
		Administrator a1 = new Administrator("admin","admin");
		Administrator a2 = new Administrator("admin","admin");
		
		assertEquals(a1,a2);
	}
	
	/**
	 * Testa il funzionameto del metodo equals di Administrator nel caso di confronto tra due Administrator diversi.
	 */
	@Test
	void testNotEquals() {
		Administrator a1 = new Administrator("admin","admin");
		Administrator a2 = new Administrator("admin","test");
		
		assertNotEquals(a1,a2);
	}
}
