//
//  AddressGeocodingApp.swift
//  AddressGeocoding
//
//  Created by Nom4D on 20/03/2023.
//

import SwiftUI

@main
struct AddressGeocodingApp: App {
    @StateObject private var geocoderHandler: GeocoderHandler = GeocoderHandler()

    var body: some Scene {
        WindowGroup {
            ContentView()
                .onAppear {
                    geocoderHandler.knownLocations = geocoderHandler.loadFromLocalStorage()
                }
                .environmentObject(geocoderHandler)
        }
    }
}
