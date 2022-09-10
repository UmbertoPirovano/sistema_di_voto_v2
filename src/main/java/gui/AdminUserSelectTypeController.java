package gui;

import java.io.IOException;
import java.net.URL;
import java.util.ResourceBundle;

import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.fxml.Initializable;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.ChoiceBox;
import javafx.stage.Stage;

public class AdminUserSelectTypeController implements Initializable {

    @FXML
    private Button confirmButton;

    @FXML
    private ChoiceBox<String> typeChoice;

    @FXML
    void confirmType(ActionEvent event) {
    	String type = typeChoice.getValue();
    	if(type.equals("Amministratore")) {
    		try {
    			confirmButton.getScene().getWindow().hide();
        		Parent root = FXMLLoader.load(getClass().getResource("AdminAdministratorEditor.fxml"));
                Stage stage = new Stage();
            	stage.setTitle("Sistema di voto elettronico - Administrator editor");
            	stage.setScene(new Scene(root, 500, 400));
            	stage.setResizable(false);
            	stage.show();
    		}catch (IOException e) {
    			System.out.println(e.getMessage());
    		}
    	}else if(type.equals("Elettore")){
    		try {
    			confirmButton.getScene().getWindow().hide();
        		Parent root = FXMLLoader.load(getClass().getResource("AdminElectorEditor.fxml"));
                Stage stage = new Stage();
            	stage.setTitle("Sistema di voto elettronico - Elector editor");
            	stage.setScene(new Scene(root, 500, 400));
            	stage.setResizable(false);
            	stage.show();
    		}catch (IOException e) {
    			System.out.println(e.getMessage());
    		}
    	}else {
    		throw new IllegalArgumentException("Tipo non supportato");
    	}
    }

	@Override
	public void initialize(URL location, ResourceBundle resources) {
		typeChoice.getItems().addAll("Elettore", "Amministratore");
		typeChoice.setValue("Elettore");
	}

}
