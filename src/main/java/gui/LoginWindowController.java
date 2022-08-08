package gui;

import java.io.IOException;
import java.net.URL;
import java.util.Objects;
import java.util.ResourceBundle;

import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.fxml.Initializable;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.ChoiceBox;
import javafx.scene.control.Label;
import javafx.scene.control.PasswordField;
import javafx.scene.control.TextField;
import javafx.scene.input.MouseEvent;
import javafx.scene.layout.Pane;
import javafx.stage.Stage;
import system.SystemEvote;
import users.Administrator;
import users.Elector;
import users.User;

public class LoginWindowController implements Initializable {

    @FXML
    private Pane container;

    @FXML
    private ChoiceBox<?> modeSelection;

    @FXML
    private Button settingsButton;

    @FXML
    private Label statusLabel;

    @FXML
    private Button submitButton;

    @FXML
    private TextField userField;
    
    @FXML
    private PasswordField pwField;

    @FXML
    void setFocus(MouseEvent event) {

    }

    @FXML
    void submit(ActionEvent event) {
    	String username = userField.getText();
    	String password = pwField.getText();
    	try {
	    	SystemEvote.getInstance().login(username, password);
	    	System.out.println("Login successfull");
	    	User u = SystemEvote.getInstance().getSession().getUser();
	    	if(u instanceof Administrator) {
	    		showAdministratorMenu();
	    	} else if(u instanceof Elector) {
	    		showElectorMenu();
	    	} else {
	    		throw new IllegalArgumentException("Tipo non supportato");
	    	}
    	} catch(IllegalArgumentException e) {
    		statusLabel.setText(e.getMessage());
    	} catch(Exception e) {
    		showErrorMessage(e.getMessage());
    	}
    }

	@Override
	public void initialize(URL location, ResourceBundle resources) {
		// TODO Auto-generated method stub
		
	}
	
	/**
	 * Apre il menù amministratore e chiude la schermata corrente.
	 */
	private void showAdministratorMenu() {
		try {
			submitButton.getScene().getWindow().hide();
    		Parent root = FXMLLoader.load(getClass().getResource("AdminMenu.fxml"));
            Stage stage = new Stage();
        	stage.setTitle("Sistema di voto elettronico - Menù amministratore");
        	stage.setScene(new Scene(root, 900, 700));
        	stage.setResizable(false);
        	stage.show();
		}catch (IOException e) {
			System.out.println(e.getMessage());
		}
	}
	
	/**
	 * Apre l'interfaccia dedicata all'elettore e chiude la schermata corrente.
	 */
	private void showElectorMenu() {
		try {
			submitButton.getScene().getWindow().hide();
    		Parent root = FXMLLoader.load(getClass().getResource("ElectorPollList.fxml"));
            Stage stage = new Stage();
        	stage.setTitle("Sistema di voto elettronico - Selezione votazione");
        	stage.setScene(new Scene(root, 900, 700));
        	stage.setResizable(false);
        	stage.show();
		}catch (IOException e) {
			System.out.println(e.getMessage());
		}
	}
	
	private void showErrorMessage(String s) {
		Objects.requireNonNull(s);
		String msg = "ERROR:\n\n";
		msg += s;
		try {
			FXMLLoader loader = new FXMLLoader(getClass().getResource("GeneralMessage.fxml"));
    		GeneralMessageController controller = new GeneralMessageController(msg);
    		loader.setController(controller);
    		Parent root = loader.load();
            Stage stage = new Stage();
        	stage.setTitle("ERROR");
        	stage.setScene(new Scene(root, 600, 400));
        	stage.setResizable(false);
        	stage.show();
		} catch (Exception e) {
			showErrorMessage(e.getMessage());
			e.printStackTrace();
		}
	}
}

