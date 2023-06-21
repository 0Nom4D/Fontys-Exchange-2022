//
//  ContentView.swift
//  AddressGeocoding
//
//  Created by Nom4D on 20/03/2023.
//

import SwiftUI
import CoreLocation

extension UIApplication {
    func endEditing() {
        sendAction(#selector(UIResponder.resignFirstResponder), to: nil, from: nil, for: nil)
    }
}

struct ContentView: View {
    @State private var expanded: Bool = false
    @State private var address: String = ""

    @EnvironmentObject private var geocoderHandler: GeocoderHandler

    var body: some View {
        GeometryReader { proxy in
            ZStack {
                MapViewer()
                    .edgesIgnoringSafeArea(.all)
                    .onTapGesture {
                        UIApplication.shared.endEditing()
                    }
                BottomDrawer()
                    .accessibilityIdentifier("bottomDrawer")
            }
            .edgesIgnoringSafeArea(.all)
        }
        .environmentObject(geocoderHandler)
    }
}

struct ContentView_Previews: PreviewProvider {
    static var previews: some View {
        ContentView()
    }
}
